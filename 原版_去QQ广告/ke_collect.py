"""验证码样本、共享学习事件和训练数据的云端同步。"""
from __future__ import annotations
import hashlib
import io
import json
import os
import random
import shutil
import threading
import time
import zipfile
import urllib.parse as _up
import urllib.request as _ur
SERVER = 'http://47.79.117.138:5888'
COLLECT_URL = SERVER + '/collect'
SHARE_URL = SERVER + '/share_events'
TABLE_URL = SERVER + '/share_table'
TRAIN_URL = SERVER + '/train_data'
TRAIN_STAT_URL = SERVER + '/train_stat'
VERSION = 'v26.8.21'
MIN_INTERVAL = 600
MAX_PER_PACK = 120
MAX_EVENTS = 50
TABLE_CHARSET = '023456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
MAX_TABLE = 5000
MAX_TABLE_SIZE = 2 * 1024 * 1024
_SAMPLE_CHARSET = TABLE_CHARSET
_SAMPLE_LOCK = threading.Lock()
_EVT_LOCK = threading.Lock()
TRAIN_STAT = None

def _set_attr(path, attr):
    try:
        import ctypes as _ct
        _ct.windll.kernel32.SetFileAttributesW.argtypes = [_ct.c_wchar_p, _ct.c_uint]
        _ct.windll.kernel32.SetFileAttributesW.restype = _ct.c_int
        return _ct.windll.kernel32.SetFileAttributesW(path, attr)
    except Exception:
        return 0

def _unhide_file(path):
    try:
        if os.path.exists(path):
            _set_attr(path, 0x20)
    except Exception:
        pass

def _ke_hidden_dir(base):
    directory = os.path.join(base, '.ke')
    try:
        if not os.path.isdir(directory):
            os.makedirs(directory, exist_ok=True)
            _set_attr(directory, 0x02)
        for name in ('共享纠正表.json', '共享事件'):
            old_path = os.path.join(base, name)
            new_path = os.path.join(directory, name)
            if os.path.exists(old_path) and not os.path.exists(new_path):
                try:
                    _unhide_file(old_path)
                    shutil.move(old_path, new_path)
                except Exception:
                    pass
    except Exception:
        pass
    return directory

def _hide_file(path):
    return None

def _paths(base):
    try:
        from ke_engine import SHOT_DIR
        root = SHOT_DIR
    except Exception:
        root = os.path.join(base, 'logs', 'img')
    return {'crop': os.path.join(root, 'crop'), 'manual': os.path.join(root, 'manual'), 'uploaded': os.path.join(root, 'uploaded')}

def _is_valid_sample_name(filename):
    if filename.startswith('captcha-crop_'):
        answer = filename.split('_', 2)[1]
        return 1 <= len(answer) <= 8 and all((character in _SAMPLE_CHARSET for character in answer))
    if filename.startswith('captcha-manual_'):
        return True
    return False

def _pending_files(directories):
    pending = []
    for directory in (directories['crop'], directories['manual']):
        if not os.path.isdir(directory):
            continue
        for filename in os.listdir(directory):
            path = os.path.join(directory, filename)
            if not os.path.isfile(path):
                continue
            if not filename.lower().endswith(('.png', '.jpg', '.jpeg')):
                continue
            if directory == directories['crop'] and (not _is_valid_sample_name(filename)):
                continue
            pending.append((filename, path))
    return pending

def _make_pack(items):
    buffer = io.BytesIO()
    with zipfile.ZipFile(buffer, 'w', zipfile.ZIP_DEFLATED) as archive:
        for index, (name, path) in enumerate(items):
            try:
                with open(path, 'rb') as stream:
                    data = stream.read()
                if not name.startswith('captcha-crop_') and (not name.startswith('captcha-manual_')):
                    name = 'captcha-manual_%s_%d.png' % (time.strftime('%Y%m%d%H%M%S'), index)
                archive.writestr(name, data)
            except Exception:
                continue
    return buffer.getvalue()

def _upload(raw, key, hwid):
    boundary = '----KE' + hashlib.md5(str(time.time()).encode()).hexdigest()[:12]
    body = io.BytesIO()

    def write(value):
        body.write(value.encode() if isinstance(value, str) else value)
    write(f'--{boundary}\r\nContent-Disposition: form-data; name="key"\r\n\r\n{key}\r\n')
    write(f'--{boundary}\r\nContent-Disposition: form-data; name="ver"\r\n\r\n{VERSION}\r\n')
    write(f'--{boundary}\r\nContent-Disposition: form-data; name="hwid"\r\n\r\n{hwid}\r\n')
    write(f"""--{boundary}\r\nContent-Disposition: form-data; name="file"; filename="c_{time.strftime('%Y%m%d_%H%M%S')}.zip"\r\nContent-Type: application/zip\r\n\r\n""")
    write(raw)
    write('\r\n--%s--\r\n' % boundary)
    request = _ur.Request(COLLECT_URL, data=body.getvalue(), headers={'Content-Type': 'multipart/form-data; boundary=%s' % boundary})
    try:
        response = json.loads(_ur.urlopen(request, timeout=10).read().decode('utf-8', 'ignore'))
    except Exception as exc:
        return (False, str(exc))
    return (bool(response.get('ok')), response.get('reason', ''))

def upload_once(base, key, hwid):
    if not key:
        return 0
    if not _SAMPLE_LOCK.acquire(blocking=False):
        return 0
    try:
        return _upload_once_locked(base, key, hwid)
    finally:
        _SAMPLE_LOCK.release()

def _upload_once_locked(base, key, hwid):
    directories = _paths(base)
    items = _pending_files(directories)
    if not items:
        return 0
    total_sent = 0
    for index in range(0, len(items), MAX_PER_PACK):
        chunk = items[index:index + MAX_PER_PACK]
        raw = _make_pack(chunk)
        if len(raw) < 30:
            continue
        try:
            ok, _message = _upload(raw, key, hwid)
        except Exception:
            continue
        if not ok:
            continue
        upload_directory = directories['uploaded']
        try:
            os.makedirs(upload_directory, exist_ok=True)
        except Exception:
            pass
        for name, path in chunk:
            try:
                shutil.move(path, os.path.join(upload_directory, name))
            except Exception as exc:
                print(f'[collect] 上传成功但移动失败 {path}: {exc}')
        total_sent += len(chunk)
    return total_sent

def _post_json(url, payload, timeout=10):
    request = _ur.Request(url, data=json.dumps(payload).encode('utf-8'), headers={'Content-Type': 'application/json'})
    try:
        response = json.loads(_ur.urlopen(request, timeout=timeout).read().decode('utf-8', 'ignore'))
    except Exception as exc:
        return (None, str(exc))
    return (response, None)

def _valid_shared_key(key):
    return isinstance(key, str) and len(key) == 4 and (key[1:3] == '->') and (key[0] in TABLE_CHARSET) and (key[3] in TABLE_CHARSET) and (key[0] != key[3])

def _upload_events(base, key, hwid):
    if not _EVT_LOCK.acquire(blocking=False):
        return 0
    try:
        return _upload_events_locked(base, key, hwid)
    finally:
        _EVT_LOCK.release()

def _upload_events_locked(base, key, hwid):
    directory = os.path.join(_ke_hidden_dir(base), '共享事件')
    if not key or not os.path.isdir(directory):
        return 0
    try:
        files = sorted((filename for filename in os.listdir(directory) if filename.startswith('evt_') and filename.endswith('.json')))
    except Exception:
        return 0
    if not files:
        return 0
    events = []
    for filename in files[:MAX_EVENTS]:
        try:
            with open(os.path.join(directory, filename), 'r', encoding='utf-8') as stream:
                event = json.load(stream)
            found, original = (event.get('f'), event.get('o'))
            if found and original and (found != original) and (found in TABLE_CHARSET) and (original in TABLE_CHARSET):
                item = {'f': found, 'o': original, 'n': int(event.get('n', 2))}
                if event.get('veto'):
                    item['veto'] = 1
                image = event.get('img')
                if isinstance(image, str) and len(image) <= 200 * 1024:
                    item['img'] = image
                events.append(item)
        except Exception:
            continue
    if not events:
        return 0
    response, _error = _post_json(SHARE_URL, {'key': key, 'hwid': hwid, 'ver': VERSION, 'events': events})
    if not response or not response.get('ok'):
        return 0
    sent = 0
    for filename in files[:MAX_EVENTS]:
        try:
            os.remove(os.path.join(directory, filename))
            sent += 1
        except Exception:
            pass
    return sent

def _fetch_shared_table(base, key, hwid):
    if not key:
        return 0
    try:
        url = TABLE_URL + '?' + _up.urlencode({'key': key, 'hwid': hwid or ''})
        raw = _ur.urlopen(url, timeout=10).read()
        if len(raw) > MAX_TABLE_SIZE:
            return 0
        response = json.loads(raw.decode('utf-8', 'ignore'))
        if not isinstance(response, dict) or not response.get('ok'):
            return 0
        table = response.get('table')
        if not isinstance(table, dict):
            return 0
        clean = {}
        for item_key, count in table.items():
            if _valid_shared_key(item_key) and isinstance(count, int) and (1 <= count <= 100000):
                clean[item_key] = count
                if len(clean) >= MAX_TABLE:
                    break
    except Exception:
        return 0
    try:
        path = os.path.join(_ke_hidden_dir(base), '共享纠正表.json')
        temporary = path + '.tmp'
        with open(temporary, 'w', encoding='utf-8') as stream:
            json.dump(clean, stream, ensure_ascii=False)
        os.replace(temporary, path)
        _hide_file(path)
        return len(clean)
    except Exception:
        return 0

def fetch_train_stat(key, hwid):
    if not key:
        return None
    try:
        url = TRAIN_STAT_URL + '?' + _up.urlencode({'key': key, 'hwid': hwid or ''})
        response = json.loads(_ur.urlopen(url, timeout=10).read().decode('utf-8', 'ignore'))
        if response.get('ok') and isinstance(response.get('fp'), str):
            return {'fp': response['fp'], 'count': int(response.get('count', 0))}
    except Exception:
        pass
    return None

def fetch_train_data(key, hwid, save_dir, fp_file):
    if not key:
        raise RuntimeError('未激活, 仅管理员可训练')
    fingerprint = fetch_train_stat(key, hwid)
    if fingerprint and os.path.isfile(fp_file):
        try:
            with open(fp_file, 'r') as stream:
                if stream.read().strip() == fingerprint['fp'] and _dir_has_img(save_dir):
                    return _dir_count(save_dir)
        except Exception:
            pass
    url = TRAIN_URL + '?' + _up.urlencode({'key': key, 'hwid': hwid or ''})
    try:
        request = _ur.Request(url)
        response = _ur.urlopen(request, timeout=60)
        if response.getcode() == 403:
            raise RuntimeError('仅管理员账号可训练')
        raw = response.read()
    except RuntimeError:
        raise
    except Exception as exc:
        raise RuntimeError('云端样本拉取失败: %s' % exc) from exc
    if len(raw) < 100:
        raise RuntimeError('云端样本为空')
    try:
        if os.path.isdir(save_dir):
            for filename in os.listdir(save_dir):
                try:
                    os.remove(os.path.join(save_dir, filename))
                except Exception:
                    pass
        os.makedirs(save_dir, exist_ok=True)
    except Exception:
        pass
    count = 0
    with zipfile.ZipFile(io.BytesIO(raw)) as archive:
        for name in archive.namelist():
            base_name, extension = os.path.splitext(name)
            if extension.lower() not in ('.png', '.jpg', '.jpeg'):
                continue
            data = archive.read(name)
            if len(data) < 100:
                continue
            try:
                target = os.path.join(save_dir, 'c_' + base_name[:8] + extension.lower())
                with open(target, 'wb') as stream:
                    stream.write(data)
                count += 1
            except Exception:
                pass
    try:
        with open(fp_file, 'w') as stream:
            stream.write(fingerprint['fp'] if fingerprint else '')
    except Exception:
        pass
    return count

def _dir_has_img(directory):
    try:
        return any((name.lower().endswith(('.png', '.jpg')) for name in os.listdir(directory)))
    except Exception:
        return False

def _dir_count(directory):
    try:
        return len([name for name in os.listdir(directory) if name.lower().endswith(('.png', '.jpg'))])
    except Exception:
        return 0

def start_collector(settings_getter):

    def loop():
        global TRAIN_STAT
        time.sleep(30)
        last_upload = 0.0
        last_fetch = -1000000000.0
        fetch_interval = 21600 + random.uniform(-900, 900)
        while True:
            try:
                now = time.time()
                settings = settings_getter() if callable(settings_getter) else {}
                key = (settings.get('activate_key') or '').strip()
                hwid = settings.get('activate_hwid') or ''
                if not hwid:
                    from ke_engine import stable_hwid
                    hwid = stable_hwid()
                base = settings.get('_script_dir') or _default_base()
                if now - last_upload >= MIN_INTERVAL:
                    last_upload = now
                    upload_once(base, key, hwid)
                    _upload_events(base, key, hwid)
                if now - last_fetch >= fetch_interval:
                    last_fetch = now
                    fetch_interval = 21600 + random.uniform(-900, 900)
                    _fetch_shared_table(base, key, hwid)
                    try:
                        TRAIN_STAT = fetch_train_stat(key, hwid)
                    except Exception:
                        pass
            except Exception:
                pass
            time.sleep(60)
    threading.Thread(target=loop, daemon=True).start()

def _default_base():
    try:
        from DD import SCRIPT_DIR
        return SCRIPT_DIR
    except Exception:
        return os.path.dirname(os.path.abspath(__file__))
