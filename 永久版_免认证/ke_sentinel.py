"""KE 外设自检、运行监控和节流异常上报。"""
from __future__ import annotations
import json
import os
import re
import sys
import threading
import time
import cv2
import numpy as np
from ke_collect import VERSION as SOFT_VER
from ke_engine import DEFAULT_SETTINGS, SCRIPT_DIR, VK_MAP, load_settings
from ke_mem import KeMem
REPORT_DIR = os.path.join(SCRIPT_DIR, 'logs', 'reports')
SELFCHECK_REPORT = os.path.join(SCRIPT_DIR, 'logs', '自检报告.txt')
FORBIDDEN = ('bingtop_user', 'bingtop_pwd', 'activate_key', 'activate_type', 'activate_exp', 'activate_hwid', 'activate_keys', 'bind_hwnd', 'bind_title', 'window_geo', 'online_seconds')

def _log(msg):
    print(f'[哨兵] {msg}')

def _sc1_detect():

    def hit(img_bgr, region, target_rgb, tol=30, min_px=3):
        x0, y0, x1, y1 = region
        roi = img_bgr[y0:y1, x0:x1]
        if roi.size == 0:
            return False
        target = np.array(target_rgb, dtype=np.uint8)
        lower = np.clip(target.astype(int) - tol, 0, 255).astype(np.uint8)
        upper = np.clip(target.astype(int) + tol, 0, 255).astype(np.uint8)
        return cv2.countNonZero(cv2.inRange(roi, lower[::-1], upper[::-1])) >= min_px

    def canvas(width=200, height=120, color=(0, 0, 0)):
        image = np.zeros((height, width, 3), np.uint8)
        image[:] = color
        return image
    red = (220, 60, 50)
    red_bgr = (50, 60, 220)
    cases = []
    image = canvas()
    image[10:30, 10:30] = red_bgr
    cases.append(('a目标色命中', hit(image, (0, 0, 40, 40), red), '区域内红色像素>=3 应命中'))
    image = canvas()
    cases.append(('b无目标不命中', not hit(image, (0, 0, 40, 40), red), '纯黑区不应命中'))
    image = canvas()
    image[10:30, 10:30] = (90, 100, 250)
    cases.append(('c容差外不命中', not hit(image, (0, 0, 40, 40), red), 'R差40超出±30'))
    image = canvas()
    image[10, 10] = red_bgr
    image[12, 12] = red_bgr
    cases.append(('d少于3px不命中', not hit(image, (0, 0, 40, 40), red), '2px<3 不足'))
    bad = [case for case in cases if not case[1]]
    if not bad:
        return (True, 'pass', '4/4 用例通过')
    return (False, 'fail', '检测逻辑异常: ' + '; '.join((case[2] for case in bad)))

def _sc2_driver():
    try:
        from ke_engine import KEDriverInput
        instance = KEDriverInput._CACHED_INSTANCE
        if instance is None:
            return (True, 'warn', '驱动未初始化(主流程职责, 哨兵不启动它)')
        ready = instance._call('KmIsReady')
        if ready:
            return (True, 'pass', '驱动就绪(KmIsReady=1)')
        error = instance._call('KmGetLastErrorCode')
        hint = {0: '无错误码(状态未知)', 2: '找不到设备', 5: '设备未就绪'}.get(error, '未知错误码')
        return (False, 'fail', f'驱动未就绪 错误码={error}({hint})')
    except Exception as exc:
        return (False, 'fail', f'驱动查询异常: {exc}')

def _sc3_mem(settings):
    title = settings.get('bind_title', '')
    if not title:
        return (True, 'warn', '未绑定游戏窗口(Mem自测跳过)')
    try:
        memory = KeMem(log_cb=None)
        memory.attach_by_title(title)
        if not memory.attached:
            return (True, 'warn', '游戏未运行/窗口不存在(attach 失败属正常)')
        pid, bits = (memory.pid, memory.bits)
        memory.close()
        return (True, 'pass', f'Mem只读通道正常(pid={pid} {bits}位)')
    except Exception as exc:
        return (False, 'fail', f'Mem自测异常: {exc}')

def _sc4_hotkey(settings):
    try:
        import win32api
        keys = [settings.get('hotkey_start', 'Home'), settings.get('emergency_key', 'End')]
        missing = [key for key in keys if VK_MAP.get(key) is None]
        if missing:
            return (False, 'fail', f'热键配置损坏(不在映射表): {missing}, 请到设置重选')
        for key in keys:
            win32api.GetAsyncKeyState(VK_MAP[key])
        return (True, 'pass', f"热键映射正常({', '.join(keys)})")
    except Exception as exc:
        return (False, 'fail', f'热键自测异常: {exc}')

def _sc5_config(settings):
    try:
        bad = []
        for key in DEFAULT_SETTINGS:
            if key not in settings:
                bad.append(f'缺键:{key}')
        lazy_keys = ('color_thresholds', 'rules_deleted', 'color_rules_enabled', 'memory_rules', 'captcha_cal')
        warning_missing = [key for key in lazy_keys if key not in settings]
        color_rules = settings.get('color_rules', {})
        if not isinstance(color_rules, dict):
            bad.append('color_rules 结构异常(非dict)')
        elif not color_rules:
            warning_missing.append('color_rules')
        else:
            for rule_name, groups in color_rules.items():
                if not isinstance(groups, dict):
                    bad.append(f'color_rules[{rule_name}] 结构异常(非规则组)')
                    continue
                for group_name, rules in groups.items():
                    if not isinstance(rules, list):
                        bad.append(f'color_rules[{rule_name}][{group_name}] 结构异常')
                        continue
                    for index, config in enumerate(rules):
                        coordinates_ok = all((isinstance(config.get(field), (int, float)) for field in ('x_pct', 'y_pct', 'w_pct', 'h_pct')))
                        if not coordinates_ok:
                            bad.append(f'color_rules[{rule_name}][{group_name}][{index}] 坐标字段异常')
                            break
                        if not isinstance(config.get('color'), list) or len(config.get('color', [])) != 3:
                            bad.append(f'color_rules[{rule_name}][{group_name}][{index}] color 异常')
                            break
        driver_directory = os.path.join(SCRIPT_DIR, '驱动')
        official = ['专版.lua', '无闪.lua', '窗口专版.lua', '窗口无闪.lua', '语音测试.lua']
        if os.path.isdir(driver_directory):
            missing = [filename for filename in official if not os.path.exists(os.path.join(driver_directory, filename))]
            if missing:
                bad.append(f"官方脚本缺失: {','.join(missing)}")
        if warning_missing and (not bad):
            return (True, 'warn', '配置基本完整(惰性键缺失, 首次运行将自动创建): ' + ','.join(warning_missing[:4]))
        if not bad:
            return (True, 'pass', '配置完整')
        return (False, 'fail', '; '.join(bad[:5]))
    except Exception as exc:
        return (False, 'fail', f'配置自测异常: {exc}')

def run_selfcheck(settings=None, log=None):
    global _log
    if log:
        _log = log
    settings = settings if settings is not None else load_settings()
    steps = [('1_detect', lambda: _sc1_detect()), ('2_driver', lambda: _sc2_driver()), ('3_mem', lambda: _sc3_mem(settings)), ('4_hotkey', lambda: _sc4_hotkey(settings)), ('5_config', lambda: _sc5_config(settings))]
    items = []
    for name, function in steps:
        try:
            items.append((name, function()))
        except Exception as exc:
            items.append((name, (False, 'fail', f'自测异常: {exc}')))
    passed = sum((1 for _, (_ok, level, _message) in items if level == 'pass'))
    warned = sum((1 for _, (_ok, level, _message) in items if level == 'warn'))
    failed = sum((1 for _, (_ok, level, _message) in items if level == 'fail'))
    for name, (_ok, level, message) in items:
        _log(f'自测 {name}: [{level}] {message}')
    _log(f'自检完成: {passed} 过 {warned} 警 {failed} 挂')
    report = {'ts': time.strftime('%Y-%m-%d %H:%M:%S'), 'ver': 'pkg' if getattr(sys, '_MEIPASS', None) else 'src', 'items': {name: {'ok': ok, 'level': level, 'msg': message} for name, (ok, level, message) in items}, 'summary': {'pass': passed, 'warn': warned, 'fail': failed}}
    try:
        os.makedirs(os.path.dirname(SELFCHECK_REPORT), exist_ok=True)
        with open(SELFCHECK_REPORT, 'w', encoding='utf-8') as stream:
            json.dump(report, stream, ensure_ascii=False, indent=1)
    except Exception as exc:
        _log(f'自检报告落盘失败: {exc}')
    return items

def start(app):
    global _APP
    _APP = app
    threading.Thread(target=_selfcheck_bg, args=(app,), daemon=True, name='sentinel_selfcheck').start()
    threading.Thread(target=_monitor_loop, args=(app,), daemon=True, name='sentinel_monitor').start()

def _selfcheck_bg(app):
    time.sleep(2)
    run_selfcheck(settings=app.settings, log=app._log)

def run_selfcheck_only():
    items = run_selfcheck()
    failed = sum((1 for _, (_ok, level, _message) in items if level == 'fail'))
    sys.exit(1 if failed else 0)
_PROBE = re.compile('\\[探针\\] 整体 命中(\\d+)/(\\d+)')
_PROBE_NOFRAME = re.compile('\\[探针\\] 帧不可用')
_PROBE_EMPTY = re.compile('\\[探针\\] 无规则')
_CAP_DONE = re.compile('\\[打码\\] 完成 →')
_CAP_FAIL = re.compile('\\[打码\\] (本地答案 .*错\\(|冰拓答案 .*错\\(|弹窗仍在|OCR失败|.*停止操作)')
_ALERT_COOLDOWN = {}
_MON = threading.Lock()

def _alert(app, kind, msg):
    now = time.time()
    with _MON:
        if now - _ALERT_COOLDOWN.get(kind, 0) < 10:
            return None
        _ALERT_COOLDOWN[kind] = now
    try:
        target = app if app is not None else _APP
        if target is not None:
            target._log(f'[哨兵] 告警[{kind}] {msg}')
        else:
            _log(f'告警[{kind}] {msg}')
    except Exception:
        pass
    try:
        _push_report(_snapshot(app, kind, msg))
    except Exception:
        return None

class _ProbeMonitor:

    def __init__(self, log_path):
        self._path = log_path
        self._fp = None
        self._pos = 0
        self._reopen()

    def _reopen(self):
        try:
            self._fp = open(self._path, 'rb')
            self._fp.seek(0, 2)
            self._pos = self._fp.tell()
        except Exception:
            self._fp = None

    def read_lines(self):
        if self._fp is None:
            self._reopen()
            return []
        try:
            self._fp.seek(self._pos)
            data = self._fp.read()
            self._pos = self._fp.tell()
            if not data:
                try:
                    if self._pos > os.path.getsize(self._path):
                        self._reopen()
                except Exception:
                    pass
                return []
            return data.decode('utf-8', 'replace').splitlines()
        except Exception:
            self._reopen()
            return []

    def close(self):
        try:
            if self._fp:
                self._fp.close()
        finally:
            self._fp = None

def _monitor_loop(app):
    probe = None
    captcha_monitor = None
    hits = []
    misses = []
    flips = []
    last_probe_ts = 0.0
    last_flip_state = None
    captcha_done = []
    captcha_fail = []
    captcha_state = {'alerted': 0.0}
    next_heartbeat = 0.0
    time.sleep(2)
    while True:
        try:
            now = time.time()
            if captcha_monitor is None:
                captcha_monitor = _ProbeMonitor(os.path.join(SCRIPT_DIR, '日志.txt'))
            for line in captcha_monitor.read_lines():
                if _CAP_DONE.search(line):
                    captcha_done.append(now)
                elif _CAP_FAIL.search(line):
                    captcha_fail.append(now)
            _captcha_check(app, captcha_done, captcha_fail, now, captcha_state)
            runner = getattr(app, 'runner', None)
            active = runner is not None and getattr(runner, '_async_thread', None) is not None and (not getattr(runner, '_async_paused', False))
            if active:
                if probe is None:
                    probe = _ProbeMonitor(os.path.join(SCRIPT_DIR, '日志.txt'))
                for line in probe.read_lines():
                    match = _PROBE.search(line)
                    if not match:
                        continue
                    hit_count, need_count = (int(match.group(1)), int(match.group(2)))
                    last_probe_ts = now
                    state = 'hit' if hit_count >= need_count else 'miss'
                    if state == 'hit':
                        hits.append((now, hit_count, need_count))
                    else:
                        misses.append((now, hit_count))
                    if last_flip_state != state:
                        flips.append(now)
                    last_flip_state = state
                while hits and hits[0][0] < now - 60:
                    hits.pop(0)
                while misses and misses[0][0] < now - 60:
                    misses.pop(0)
                while flips and flips[0] < now - 60:
                    flips.pop(0)
                _probe_check(app, hits, misses, flips, now, last_probe_ts)
            else:
                if probe is not None:
                    probe.close()
                    probe = None
                hits[:] = []
                misses[:] = []
                flips[:] = []
                last_flip_state, last_probe_ts = (None, 0.0)
            if now >= next_heartbeat:
                next_heartbeat = now + 10
                _heartbeat_check(app, now)
        except Exception as exc:
            _alert(app, 'monitor_err', f'监控异常: {exc}')
        time.sleep(2)

def _captcha_check(app, done_ts, fail_ts, now, state):
    while done_ts and done_ts[0] < now - 3600:
        done_ts.pop(0)
    while fail_ts and fail_ts[0] < now - 3600:
        fail_ts.pop(0)
    if len(fail_ts) >= 10 and len(done_ts) < 3:
        if state['alerted'] == 0.0 or now - state['alerted'] > 7200:
            state['alerted'] = now
            _alert(
                app,
                'captcha_dead',
                '打码链路疑似失效(60分钟内完成%d次/失败%d次), '
                '建议人工确认识别通道(本地模型/冰拓)' % (len(done_ts), len(fail_ts)),
            )
    elif done_ts:
        state['alerted'] = 0.0

def _probe_check(app, hits, misses, flips, now, last_probe_ts):
    if len(flips) >= 20:
        _alert(app, 'probe_flap', f'锁定-丢失高频交替({len(flips)}次/60s) 疑似目标识别不稳定')
    if last_probe_ts and now - last_probe_ts > 30:
        _alert(app, 'probe_silence', f'检测线程疑似卡死({int(now - last_probe_ts)}s 无探针输出), 建议重启软件')
    if hits and len(misses) >= 30:
        _alert(app, 'probe_miss_zero', f'曾命中后 60s 未命中×{len(misses)} 可能取色失效或暂无可打目标')
_HEARTBEATS = {}

def _heartbeat_check(app, now):
    for name, heartbeat in list(_HEARTBEATS.items()):
        try:
            if heartbeat.get('thread'):
                if not heartbeat['thread'].is_alive():
                    _alert(app, 'thread_dead', f'线程[{name}]已退出')
                    _HEARTBEATS.pop(name, None)
            elif now - heartbeat.get('last_beat', 0) > 15:
                _alert(app, 'thread_dead', f'线程[{name}]15s 无心跳(主线程卡死?)')
        except Exception:
            continue

def register(name, thread=None):
    _HEARTBEATS[name] = {'thread': thread, 'last_beat': time.time()}

def unregister(name):
    _HEARTBEATS.pop(name, None)

def beat(name):
    heartbeat = _HEARTBEATS.get(name)
    if heartbeat:
        heartbeat['last_beat'] = time.time()
_HK = {'press': 0.0, 'deltas': []}

def on_hotkey_press():
    _HK['press'] = time.time()

def on_hotkey_toggle():
    now = time.time()
    if _HK['press']:
        delta = now - _HK['press']
        if delta > 0:
            _HK['deltas'].append(delta)
            if len(_HK['deltas']) > 30:
                _HK['deltas'].pop(0)
            average = sum(_HK['deltas']) / len(_HK['deltas'])
            if delta > 2.0 or average > 0.5:
                _alert(None, 'hotkey_lag', f'热键响应延迟异常(单次{int(delta * 1000)}ms 均值{int(average * 1000)}ms) 疑似UI队列积压')
    _HK['press'] = 0.0
REPORT_URL = ''
QUEUE_FILE = os.path.join(REPORT_DIR, 'queue.json')
QUEUE_MAX = 5
THROTTLE_HOURS = 1
DETAIL_MAX = 2000
_SNAP_KEYS = ('hotkey_start', 'emergency_key', 'input_mode', 'fix_delay_ms', 'color_thresholds', 'color_rules_enabled', 'memory_rules', 'captcha_cal', 'rate')
_QUEUE_LOCK = threading.Lock()
_queue = None
_report_times = {}
_APP = None

def _hwid(settings):
    try:
        value = (settings or {}).get('activate_hwid') or ''
        if not value:
            from ke_engine import stable_hwid
            value = stable_hwid()
        return value[:64]
    except Exception:
        return 'unknown'

def _erase_sensitive(line):
    for key in FORBIDDEN:
        line = re.sub('(?i)\\b%s\\b["\\\']?\\s*[=:：]\\s*["\\\']?[^\\s,;]+' % re.escape(key), '%s=***' % key, line)
    return re.sub('KE-[A-Z0-9]{5}(?:-[A-Z0-9]{5}){3}', 'KE-***', line)

def _snapshot(app, kind, detail):
    settings = getattr(app, 'settings', None) or {}
    snapshot = {}
    for key in _SNAP_KEYS:
        value = settings.get(key)
        if value is not None:
            try:
                json.dumps(value)
                snapshot[key] = value
            except Exception:
                pass
    lines = []
    try:
        keywords = ('[探针]',) if kind.startswith('probe') else (kind.split('_')[0],)
        for line in reversed(list(getattr(app, '_log_lines', None) or [])):
            if any((keyword in line for keyword in keywords)):
                lines.append(_erase_sensitive(line))
                if len(lines) >= 20:
                    break
    except Exception:
        pass
    return {'kind': kind, 'detail': detail[:DETAIL_MAX], 'snap': snapshot, 'logs': lines, 'ver': SOFT_VER, 'hwid': _hwid(settings), 'ts': time.strftime('%Y-%m-%d %H:%M:%S'), 'python': '%d.%d' % sys.version_info[:2], 'os': sys.platform}

def _load_queue():
    global _queue
    if _queue is not None:
        return _queue
    try:
        if os.path.exists(QUEUE_FILE):
            with open(QUEUE_FILE, 'r', encoding='utf-8') as stream:
                _queue = json.load(stream)
    except Exception:
        pass
    if not isinstance(_queue, list):
        _queue = []
    return _queue

def _save_queue():
    try:
        os.makedirs(REPORT_DIR, exist_ok=True)
        temporary = QUEUE_FILE + '.tmp'
        with open(temporary, 'w', encoding='utf-8') as stream:
            json.dump(_queue, stream, ensure_ascii=False)
        os.replace(temporary, QUEUE_FILE)
    except Exception:
        return None

def _push_report(body):
    kind = body['kind']
    now = time.time()
    with _QUEUE_LOCK:
        if now - _report_times.get(kind, 0) < THROTTLE_HOURS * 3600:
            return False
        _report_times[kind] = now
        queue = _load_queue()
        queue.append(body)
        if len(queue) > QUEUE_MAX:
            del queue[:len(queue) - QUEUE_MAX]
        _save_queue()
    return True

def _post_report(body):
    return (False, '永久版已关闭远程上报')
    key = ''
    try:
        key = (_APP.settings.get('activate_key') or '').strip() if _APP else ''
    except Exception:
        pass
    if not key:
        return (False, '无激活码')
    detail = {'detail': body.get('detail', ''), 'snap': body.get('snap', {}), 'logs': body.get('logs', [])}
    form = _up.urlencode({'key': key, 'hwid': body.get('hwid', ''), 'ver': body.get('ver', ''), 'kind': body['kind'], 'detail': json.dumps(detail, ensure_ascii=False)})
    request = _ur.Request(REPORT_URL, data=form.encode('utf-8'))
    response = json.loads(_ur.urlopen(request, timeout=10).read().decode('utf-8', 'ignore'))
    return (bool(response.get('ok')), str(response.get('reason', '')))

def _flush_once():
    global _queue
    with _QUEUE_LOCK:
        queue = list(_load_queue())
        if not queue:
            return None
        _queue[:] = []
    kept = []
    for body in queue:
        try:
            ok, reason = _post_report(body)
            if ok:
                continue
            body['_fail'] = body.get('_fail', 0) + 1
            if body['_fail'] >= 3:
                _log(f"上报被拒3次丢弃: {body['kind']} ({reason})")
                continue
            kept.append(body)
        except Exception:
            kept.append(body)
    with _QUEUE_LOCK:
        _queue[:] = kept + _queue
        _save_queue()

def _flush_loop():
    while True:
        try:
            time.sleep(60)
            _flush_once()
        except Exception:
            time.sleep(10)
