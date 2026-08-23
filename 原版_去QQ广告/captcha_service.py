"""
验证码服务 — 老版本算法 + 冰拓 API

检测：白底检测、饱和度、Canny 边缘和 AI 模型；
识别：本地 OCR 优先，冰拓云端回退；
输入：自动定位输入框和确认按钮，粘贴后验证弹窗是否消失。
"""
import base64
import ctypes
from ctypes import wintypes
from datetime import datetime
import glob
import hashlib
import io
import json
import os
import random
import re
import threading
import time
import cv2
import numpy as np
import requests
from PIL import Image, ImageGrab
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))

def _set_attr(path, attr):
    try:
        ctypes.windll.kernel32.SetFileAttributesW.argtypes = [ctypes.c_wchar_p, ctypes.c_uint]
        ctypes.windll.kernel32.SetFileAttributesW.restype = ctypes.c_int
        return ctypes.windll.kernel32.SetFileAttributesW(path, attr)
    except Exception:
        return 0

def _unhide_file(path):
    try:
        if os.path.exists(path):
            _set_attr(path, 0x20)
    except Exception:
        pass

def _hide_file(path):
    return None

def set_clipboard(text):
    """设置 Unicode 剪贴板文本，并在所有失败路径释放句柄。"""
    user32 = ctypes.windll.user32
    kernel32 = ctypes.windll.kernel32
    user32.OpenClipboard.argtypes = [wintypes.HWND]
    user32.OpenClipboard.restype = wintypes.BOOL
    user32.EmptyClipboard.restype = wintypes.BOOL
    user32.SetClipboardData.argtypes = [wintypes.UINT, wintypes.HANDLE]
    user32.SetClipboardData.restype = wintypes.HANDLE
    user32.CloseClipboard.restype = wintypes.BOOL
    kernel32.GlobalAlloc.argtypes = [wintypes.UINT, ctypes.c_size_t]
    kernel32.GlobalAlloc.restype = wintypes.HGLOBAL
    kernel32.GlobalFree.argtypes = [wintypes.HGLOBAL]
    kernel32.GlobalFree.restype = wintypes.HGLOBAL
    handle = None
    try:
        if not user32.OpenClipboard(None):
            return False
        user32.EmptyClipboard()
        if not text:
            return True
        encoded = text.encode('utf-16-le') + b'\x00\x00'
        handle = kernel32.GlobalAlloc(0, len(encoded))
        if not handle:
            return False
        ctypes.memmove(handle, encoded, len(encoded))
        if not user32.SetClipboardData(13, handle):
            return False
        handle = None
        return True
    finally:
        try:
            user32.CloseClipboard()
        except Exception:
            pass
        if handle:
            kernel32.GlobalFree(handle)
BINGTOP_CHECK_POINTS = 'https://www.bingtop.com/ocr/check_points/'
BINGTOP_UPLOAD = 'https://www.bingtop.com/ocr/upload/'
ERROR_MESSAGES = {'captcha_service_locked': '当前账号不可用', 'core_not_connected': '服务未连接', 'window_required': '请先选择窗口', 'bingtop_required': '请填写冰拓信息', 'bingtop_auth_failed': '冰拓账号或密码错误', 'bingtop_points_insufficient': '冰拓点数不足', 'bingtop_check_failed': '冰拓校验失败', 'config_failed': '设置失败', 'start_failed': '启动失败'}
_captcha_lock = threading.Lock()
_tts_func = None

def set_tts_callback(fn):
    global _tts_func
    _tts_func = fn
_ai_state = {'status': '等待验证码', 'method': '', 'answer': '', 'conf': 0.0, 'elapsed_ms': 0, 'box': None, 'step': '', 'count_detect': 0, 'count_success': 0, 'count_fail': 0, 'ts': 0.0}
_ai_lock = threading.Lock()

def update_ai_state(**kw):
    """更新实时状态；``inc_`` 前缀表示累加计数。"""
    with _ai_lock:
        for key, value in kw.items():
            if key.startswith('inc_'):
                real_key = key[4:]
                _ai_state[real_key] = _ai_state.get(real_key, 0) + value
            else:
                _ai_state[key] = value
        _ai_state['ts'] = time.time()

def get_ai_state():
    with _ai_lock:
        return dict(_ai_state)

def format_error(error_code, message):
    if error_code in ERROR_MESSAGES:
        if message:
            return str(ERROR_MESSAGES[error_code]) + '(' + str(message) + ')'
    if not message:
        return ERROR_MESSAGES.get(error_code, '操作失败')
    else:
        return ERROR_MESSAGES.get(error_code, message)

class BingtopClient:
    """冰拓打码平台客户端。"""

    def __init__(self, username='', password='', captcha_type='1017'):
        self.username = username
        self.password = password
        self.captcha_type = captcha_type

    def check_points(self):
        if not self.username or not self.password:
            return {'success': False, 'error': 'bingtop_required'}
        try:
            response = requests.post(BINGTOP_CHECK_POINTS, data={'username': self.username, 'password': self.password, 'captchaType': self.captcha_type}, timeout=7)
            if response.status_code != 200:
                return {'success': False, 'error': 'bingtop_check_failed', 'message': f'HTTP {response.status_code}'}
            payload = response.json()
            if payload.get('code') == 0:
                data = payload.get('data')
                points = data.get('points', 0) if isinstance(data, dict) else 0
                return {'success': True, 'points': points}
            message = payload.get('message', '')
            lowered = message.lower()
            if 'password' in lowered or 'pwd' in lowered or '密码' in message or ('账号' in message) or ('用户名' in message):
                error = 'bingtop_auth_failed'
            elif 'point' in lowered or 'insufficient' in lowered or '积分' in message or ('点数' in message) or ('余额' in message):
                error = 'bingtop_points_insufficient'
            else:
                error = 'bingtop_check_failed'
            return {'success': False, 'error': error, 'message': message}
        except Exception as exc:
            return {'success': False, 'error': 'bingtop_check_failed', 'message': str(exc)}

    def solve(self, img_bgr):
        if not self.username or not self.password:
            return {'success': False, 'error': 'bingtop_required', 'text': ''}
        enlarged = cv2.resize(img_bgr, None, fx=2, fy=2, interpolation=cv2.INTER_CUBIC)
        stream = io.BytesIO()
        Image.fromarray(enlarged[:, :, ::-1]).save(stream, format='PNG')
        encoded = base64.b64encode(stream.getvalue()).decode()
        for attempt in range(2):
            if attempt > 0:
                time.sleep(random.uniform(0.2, 1.5))
            try:
                response = requests.post(BINGTOP_UPLOAD, data={'username': self.username, 'password': self.password, 'captchaData': encoded, 'captchaType': self.captcha_type}, timeout=10)
                if response.status_code != 200:
                    result = {'success': False, 'error': 'bingtop_check_failed', 'message': f'HTTP {response.status_code}', 'text': ''}
                else:
                    payload = response.json()
                    if payload.get('code') == 0:
                        data = payload.get('data')
                        data = data if isinstance(data, dict) else {}
                        text = data.get('recognition', '') or data.get('text', '') or data.get('result', '') or data.get('code', '')
                        if text:
                            return {'success': True, 'text': text, 'raw': payload}
                        result = {'success': False, 'error': 'bingtop_check_failed', 'message': '识别结果为空', 'text': ''}
                    else:
                        result = {'success': False, 'error': 'bingtop_check_failed', 'message': payload.get('message', ''), 'text': ''}
                return result
            except Exception as exc:
                if attempt == 1:
                    return {'success': False, 'error': 'bingtop_check_failed', 'message': str(exc), 'text': ''}
        return {'success': False, 'error': 'bingtop_check_failed', 'message': '识别失败', 'text': ''}

class CaptchaSolver:
    """验证码自动解决器。"""
    ROUND_SEC = 50
    REFRESH_AHEAD = 10

    def __init__(self, dd, settings=None, log_cb=None, float_cb=None, fail_cb=None, transform_cb=None):
        self.dd = dd
        if not settings:
            self.settings = {}
        else:
            self.settings = settings
        if not log_cb:
            self.log = print
        else:
            self.log = log_cb
        self.float_blink = float_cb
        self.fail_cb = fail_cb
        self.transform_cb = transform_cb
        self._busy = False
        self._busy_lock = threading.Lock()
        self._cached_frame = None
        self._cached_rect = None
        self._cached_win_frame = False
        self._no_cal_logged = False
        self._ocr = None
        self._ocr_lock = threading.Lock()
        self._offx = 0
        self._offy = 0
        self._cancel = threading.Event()
        self._last_pts_ts = 0.0
        self._session_cd_until = 0.0
        self._tried_codes = set()
        return None

    def cancel(self):
        self._cancel.set()

    def _wait(self, seconds):
        return self._cancel.wait(seconds)

    def _live_bind(self):
        try:
            import win32gui
            hwnd = self.settings.get('bind_hwnd', 0) or 0
            if hwnd and not win32gui.IsWindow(hwnd):
                from ke_engine import find_window_by_title
                new_hwnd = find_window_by_title(self.settings.get('bind_title', ''))
                if new_hwnd:
                    hwnd = new_hwnd
                    self.settings['bind_hwnd'] = new_hwnd
            return int(hwnd) if hwnd else 0
        except Exception:
            return int(self.settings.get('bind_hwnd', 0) or 0)

    def _pts_worker(self, client):
        try:
            points = client.check_points()
            if points.get('success'):
                self.log(f"[打码] 冰拓剩余点数: {points.get('points', 0)}")
            else:
                self.log(f"[打码] {format_error(points.get('error'), points.get('message'))}")
        except Exception as exc:
            self.log(f'[打码] 点数查询异常: {exc}')

    def prewarm(self):
        threading.Thread(target=self._prewarm_impl, daemon=True).start()

    def _prewarm_impl(self):
        try:
            with self._ocr_lock:
                if self._ocr is None:
                    from captcha_ocr import CaptchaOcr
                    self._ocr = CaptchaOcr()
        except Exception:
            pass

    @property
    def busy(self):
        return self._busy

    def set_cached_frame(self, frame, win_frame=False):
        self._cached_frame = frame
        self._cached_win_frame = win_frame

    def set_cached_rect(self, rects):
        self._cached_rect = rects

    def solve(self, cfg=None):
        self._cancel.clear()
        with self._busy_lock:
            if self._busy:
                return None
            self._busy = True
        threading.Thread(target=self._solve_impl, args=(cfg or {},), daemon=True).start()

    def _solve_impl(self, cfg):
        try:
            self._run(cfg)
        finally:
            self._busy = False
            try:
                self._reset_mouse()
            except Exception:
                pass

    def _reset_mouse(self):
        try:
            if getattr(self, 'driver_mode', '') == 'window':
                rects = getattr(self, '_cached_rect', None) or []
                if rects:
                    rect = rects[0]
                    x = (rect[0] + rect[2]) // 2
                    y = (rect[1] + rect[3]) // 2
                    self.log(f'[打码] 鼠标复位窗口中部({x},{y})')
                    self.dd.move_to(x, y)
                    return
            import win32api
            x = int(win32api.GetSystemMetrics(0) * 0.04)
            y = int(win32api.GetSystemMetrics(1) * 0.92)
            self.log(f'[打码] 鼠标复位左下({x},{y})')
            self.dd.move_to(x, y)
        except Exception:
            pass

    def _capture_frame(self):
        """返回 ``(BGR帧, 是否窗口帧, 窗口矩形)``。"""
        window_frame = False
        frame = None
        self._offx = self._offy = 0
        if self._cached_frame is not None:
            frame = self._cached_frame.copy()
            self._cached_frame = None
            window_frame = self._cached_win_frame
        else:
            hwnd = self._live_bind()
            if hwnd:
                try:
                    from ke_engine import capture_window_bgr
                    captured = capture_window_bgr(int(hwnd))
                    if captured[0] is not None:
                        frame, self._offx, self._offy = captured
                        window_frame = True
                except Exception:
                    pass
            if frame is None:
                raw = ImageGrab.grab()
                if raw is not None:
                    frame = np.array(raw)[:, :, :3][:, :, ::-1].copy()
        window_rect = (0, 0, 0, 0)
        hwnd = self._live_bind()
        if hwnd:
            try:
                import win32gui
                value = win32gui.GetWindowRect(int(hwnd))
                if value and value[2] - value[0] > 100 and (value[3] - value[1] > 100):
                    window_rect = value
            except Exception:
                pass
        return (frame, window_frame, window_rect)

    @staticmethod
    def _calibration_point(x_percent, y_percent, frame_shape, window_rect, window_frame):
        height, width = frame_shape[:2]
        if window_rect[2] > window_rect[0] and window_rect[3] > window_rect[1]:
            win_width = window_rect[2] - window_rect[0]
            win_height = window_rect[3] - window_rect[1]
            x = int(x_percent * win_width / 100)
            y = int(y_percent * win_height / 100)
            if not window_frame:
                x += window_rect[0]
                y += window_rect[1]
            return (x, y)
        return (int(x_percent * width / 100), int(y_percent * height / 100))

    def _locate_dialog(self, full, yolo_rects, calibration, window_rect, window_frame):
        """定位并返回 ``(ROI, (x1,y1,x2,y2))``。"""
        height, width = full.shape[:2]
        if yolo_rects and (not yolo_rects.get('captcha')):
            self.log(f'[打码] YOLO仅检出{list(yolo_rects.keys())}无弹窗框, 判为误检, 不消耗机会')
            return (None, None)
        if yolo_rects and yolo_rects.get('captcha'):
            x1, y1, x2, y2 = yolo_rects['captcha']
            box_width, box_height = (x2 - x1, y2 - y1)
            min_width = max(120, width * 0.08)
            min_height = max(80, height * 0.06)
            if box_width >= min_width and box_height >= min_height and (box_width <= width * 0.9) and (box_height <= height * 0.9):
                x1, y1 = (max(0, int(x1)), max(0, int(y1)))
                x2, y2 = (min(width, int(x2)), min(height, int(y2)))
                if x2 > x1 and y2 > y1:
                    roi = full[y1:y2, x1:x2]
                    gray = np.mean(roi, axis=2) if roi.ndim == 3 else roi
                    white_ratio = float(np.sum(gray > 200)) / gray.size
                    if roi.ndim == 3:
                        values = roi.astype(int)
                        saturation = np.max(values, axis=2) - np.min(values, axis=2)
                        colorful = float(np.sum(saturation > 50)) / saturation.size
                    else:
                        colorful = 0
                    if white_ratio >= 0.8 and colorful >= 0.03:
                        self.log(f'[打码] YOLO弹窗框 裁剪({x2 - x1}x{y2 - y1})')
                        try:
                            from ke_ai import ocr_correct_angle
                            roi = ocr_correct_angle(roi)
                        except Exception:
                            pass
                        return (roi, (x1, y1, x2, y2))
                    self.log('[打码] YOLO框预检不过, 回退校准/自动定位')
            else:
                center_x, center_y = ((x1 + x2) / 2, (y1 + y2) / 2)
                self.log(f'[打码] YOLO框几何不符({box_width}x{box_height}@({int(center_x)},{int(center_y)})), 判为误检, 不消耗机会')
        if calibration and calibration.get('crop_w'):
            point = lambda x, y: self._calibration_point(x, y, full.shape, window_rect, window_frame)
            x1, y1 = point(calibration['crop_x'], calibration['crop_y'])
            x2, y2 = point(calibration['crop_x'] + calibration['crop_w'], calibration['crop_y'] + calibration['crop_h'])
            x1, y1 = (max(0, x1), max(0, y1))
            x2, y2 = (min(width, x2), min(height, y2))
            if x2 > x1 and y2 > y1:
                roi = full[y1:y2, x1:x2]
                gray = np.mean(roi, axis=2) if roi.ndim == 3 else roi
                white_ratio = float(np.sum(gray > 200)) / gray.size
                if roi.ndim == 3:
                    values = roi.astype(int)
                    saturation = np.max(values, axis=2) - np.min(values, axis=2)
                    colorful = float(np.sum(saturation > 50)) / saturation.size
                else:
                    colorful = 0
                if white_ratio >= 0.8 and colorful >= 0.03:
                    self.log(f'[打码] 通过检测 裁剪({x2 - x1}x{y2 - y1})')
                    try:
                        from ke_ai import ocr_correct_angle
                        roi = ocr_correct_angle(roi)
                    except Exception:
                        pass
                    return (roi, (x1, y1, x2, y2))
        gray = cv2.cvtColor(full, cv2.COLOR_BGR2GRAY)
        edges = cv2.Canny(gray, 50, 150)
        contours, _ = cv2.findContours(edges, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
        best_rect = None
        best_area = 0
        for contour in contours:
            x, y, box_width, box_height = cv2.boundingRect(contour)
            area = box_width * box_height
            if 10000 < area < width * height * 0.8 and box_width > 100 and (box_height > 80) and (y < height * 0.7) and (area > best_area):
                best_area = area
                best_rect = (x, y, x + box_width, y + box_height)
        if best_rect is None:
            return (None, None)
        x1, y1, x2, y2 = best_rect
        dialog = full[y1:y2, x1:x2]
        if dialog.size == 0:
            return (None, None)
        dialog_gray = np.mean(dialog, axis=2) if dialog.ndim == 3 else dialog
        if float(np.sum(dialog_gray > 230)) / dialog_gray.size < 0.5:
            return (None, None)
        try:
            from ke_ai import ocr_correct_angle, ocr_detect_text
            detected = ocr_detect_text(dialog)
            roi = detected if detected is not None and detected.size > 0 else dialog[dialog.shape[0] // 3:, :, :]
            roi = ocr_correct_angle(roi)
        except Exception:
            roi = dialog[dialog.shape[0] // 3:, :, :]
        return (roi, best_rect)

    def _recognize(self, full, roi, box, client, local_allowed=True):
        """执行一次识别，返回 ``(答案, 来源, 置信度, 错误)``。"""
        if local_allowed:
            started = time.time()
            try:
                if self._ocr is None:
                    with self._ocr_lock:
                        if self._ocr is None:
                            from captcha_ocr import CaptchaOcr
                            self._ocr = CaptchaOcr()
                answer, confidence = self._ocr.recognize(full, box, roi=roi)
                if answer:
                    stable = True
                    if confidence >= 0.85:
                        try:
                            height, width = roi.shape[:2]
                            shifted = roi[max(0, 1):height, max(0, 2):width]
                            if shifted.size:
                                second, second_conf = self._ocr.recognize(full, box, roi=shifted)
                                stable = bool(second and second == answer)
                                if not stable:
                                    self.log(f'[打码] 本地双帧冲突 {answer}(conf={confidence:.2f}) vs {second}(conf={second_conf:.2f}), 3次内按本地试错提交')
                        except Exception:
                            stable = True
                    else:
                        self.log(f'[打码] 本地低置信 {answer} (conf={confidence:.2f}), 按本地试错提交(失败才切冰拓)')
                    if stable:
                        answer = re.sub('\\s+', '', answer)
                        raw_answer = answer
                        if confidence < 0.9:
                            answer = self._apply_confusion(answer) or answer
                        self._last_raw_answer = raw_answer
                        self.log(f'[打码] 本地识别 → {answer} (conf={confidence:.2f})')
                        update_ai_state(status='已识别', method='本地OCR', answer=answer, conf=confidence, elapsed_ms=int((time.time() - started) * 1000), step='本地模型识别', inc_count_success=1)
                        return (answer, 'local', confidence, '')
            except Exception as exc:
                self.log(f'[打码] 本地识别异常: {exc}')
        if client is None:
            return ('', '', 0.0, '本地识别未通过')
        started = time.time()
        result = client.solve(roi)
        if not result.get('success'):
            message = format_error(result.get('error'), result.get('message'))
            update_ai_state(status='识别失败', step=message, inc_count_fail=1)
            return ('', 'bt', 0.0, message)
        answer = re.sub('\\s+', '', result.get('text', ''))
        self.log(f'[打码] OCR → {answer}')
        update_ai_state(status='已识别', method='冰拓云端', answer=answer, elapsed_ms=int((time.time() - started) * 1000), step='云端回退', inc_count_success=1)
        return (answer, 'bt', 0.0, '')

    def _activate_bound_window(self):
        hwnd = self._live_bind()
        if not hwnd:
            return (True, None)
        try:
            from ke_engine import ensure_foreground
            import win32gui
            old_rect = win32gui.GetWindowRect(int(hwnd))
            foreground = False
            for _ in range(3):
                if ensure_foreground(int(hwnd)) or win32gui.GetForegroundWindow() == int(hwnd):
                    foreground = True
                    break
                if self._wait(0.6):
                    return (False, old_rect)
            if not foreground:
                self.log('[打码] 窗口激活失败×3, 跳过本轮(下轮重试)')
                return (False, old_rect)
            new_rect = win32gui.GetWindowRect(int(hwnd))
            if new_rect and new_rect[0] > -10000 and (new_rect[2] > new_rect[0]):
                self._offx, self._offy = (new_rect[0], new_rect[1])
                return (True, new_rect)
            return (True, old_rect)
        except Exception:
            return (True, None)

    def _locate_controls(self, full, box, yolo_rects, calibration, window_rect, window_frame):
        point = lambda x, y: self._calibration_point(x, y, full.shape, window_rect, window_frame)
        input_x = input_y = confirm_x = confirm_y = 0
        if calibration and calibration.get('input_x'):
            input_x, input_y = point(calibration['input_x'] + calibration.get('input_w', 0) / 2, calibration['input_y'] + calibration.get('input_h', 0) / 2)
            confirm_x, confirm_y = point(calibration.get('ok_x', 0) + calibration.get('ok_w', 0) / 2, calibration.get('ok_y', 0) + calibration.get('ok_h', 0) / 2)
        if yolo_rects:
            input_rect = yolo_rects.get('input')
            confirm_rect = yolo_rects.get('confirm')
            if input_rect and (not input_x):
                input_x = int((input_rect[0] + input_rect[2]) / 2)
                input_y = int((input_rect[1] + input_rect[3]) / 2)
            if confirm_rect and (not confirm_x):
                confirm_x = int((confirm_rect[0] + confirm_rect[2]) / 2)
                confirm_y = int((confirm_rect[1] + confirm_rect[3]) / 2)
        x1, y1, x2, y2 = box
        if not input_x:
            input_x = x1 + int((x2 - x1) * 0.3)
            input_y = y1 + int((y2 - y1) * 0.55)
        if not confirm_x:
            confirm_x = x2 - 60
            confirm_y = y2 - 40
        return (input_x, input_y, confirm_x, confirm_y)

    def _paste_and_submit(self, answer, input_x, input_y, confirm_x, confirm_y, window_frame):
        for _ in range(3):
            if self._cancel.is_set():
                return False
            for _click in range(2):
                target = (input_x + self._offx, input_y + self._offy) if window_frame else (input_x, input_y)
                self.dd.move_to(*target)
                time.sleep(random.uniform(0.3, 0.5))
                self.dd.ml_d()
                time.sleep(random.uniform(0.2, 0.4))
                self.dd.ml_u()
            if not set_clipboard(answer):
                self.log('[打码] 剪贴板写入失败, 重试')
                if self._wait(1 + random.uniform(0, 1)):
                    return False
                continue
            self._sys_keys(('ctrl', 'a'))
            time.sleep(random.uniform(0.15, 0.3))
            self._sys_keys(('backspace',))
            time.sleep(random.uniform(0.3, 0.6))
            self._sys_keys(('ctrl', 'v'))
            time.sleep(random.uniform(1.5, 2.0))
            target = (confirm_x + self._offx, confirm_y + self._offy) if window_frame else (confirm_x, confirm_y)
            self.dd.move_to(*target)
            time.sleep(random.uniform(0.3, 0.5))
            self.dd.ml_d()
            time.sleep(random.uniform(0.2, 0.4))
            self.dd.ml_u()
            return True
        self.log('[打码] 输入3轮未成功, 跳过本轮(防脏输入/空提交)')
        return False

    def _dialog_still_visible(self, original_box, original_window_frame):
        clear_frames = 0
        last_dialog = None
        for _ in range(8):
            if self._cancel.is_set():
                return (None, last_dialog)
            frame, window_frame, _ = self._capture_frame()
            if frame is None:
                if self._wait(0.5):
                    return (None, last_dialog)
                continue
            x1, y1, x2, y2 = original_box
            if window_frame == original_window_frame:
                offset_x = offset_y = 0
            else:
                offset_x = self._offx if not original_window_frame else -self._offx
                offset_y = self._offy if not original_window_frame else -self._offy
            x1, y1 = (max(0, x1 + offset_x), max(0, y1 + offset_y))
            x2, y2 = (min(frame.shape[1], x2 + offset_x), min(frame.shape[0], y2 + offset_y))
            if x2 <= x1 or y2 <= y1:
                continue
            roi = frame[y1:y2, x1:x2]
            last_dialog = roi
            gray = np.mean(roi, axis=2) if roi.ndim == 3 else roi
            still_visible = float(np.sum(gray > 200)) / gray.size > 0.3
            if still_visible:
                return (True, last_dialog)
            clear_frames += 1
            if clear_frames >= 2:
                return (False, last_dialog)
            if self._wait(0.35):
                return (None, last_dialog)
        return (True, last_dialog)

    def _run(self, cfg):
        """验证码主流程。"""
        last_dialog = None
        settings = self.settings
        if not settings.get('captcha_solve_enabled', settings.get('bingtop_enabled', True)):
            return None
        local_enabled = settings.get('local_ocr_enabled', True)
        bingtop_enabled = settings.get('bingtop_enabled', True)
        if not local_enabled and (not bingtop_enabled):
            return None
        username = settings.get('bingtop_user', '')
        password = settings.get('bingtop_pwd', '')
        client = None
        if bingtop_enabled and username and password:
            client = BingtopClient(username, password, settings.get('bingtop_type', '1017'))
        elif bingtop_enabled and (not local_enabled):
            if not self._no_cal_logged:
                self.log(f"[打码] {format_error('bingtop_required')}")
                self._no_cal_logged = True
            return None
        max_attempts = int(cfg.get('max_attempts_per_round', 12))
        alert = cfg.get('alert', True)
        auto_submit = cfg.get('auto_submit', True)
        calibration = settings.get('captcha_cal', {})
        try:
            round_seconds = float(calibration.get('round_sec', self.ROUND_SEC))
        except (TypeError, ValueError):
            round_seconds = float(self.ROUND_SEC)
        try:
            refresh_ahead = float(calibration.get('refresh_ahead', self.REFRESH_AHEAD))
        except (TypeError, ValueError):
            refresh_ahead = float(self.REFRESH_AHEAD)
        if client and time.time() - self._last_pts_ts > 60:
            self._last_pts_ts = time.time()
            threading.Thread(target=self._pts_worker, args=(client,), daemon=True).start()
        from ke_engine import SHOT_DIR
        for directory in (os.path.join(SHOT_DIR, 'crop'), os.path.join(SHOT_DIR, 'full')):
            os.makedirs(directory, exist_ok=True)
        yolo_rects = self._cached_rect
        self._cached_rect = None
        previous_start = getattr(self, '_round_t0', None)
        stale_limit = min(round_seconds * 1.5, 85.0)
        if previous_start is None or getattr(self, '_round_ok', False) or time.time() - previous_start > stale_limit:
            round_start = time.time()
            self._round_ok = False
        else:
            round_start = previous_start
        self._round_t0 = round_start
        failed_answers = []
        local_failures = 0
        cloud_failures = 0
        environment_fault = False
        exhausted = True

        def time_left():
            return round_seconds - (time.time() - round_start)

        def refresh_now(reason, full, window_rect, window_frame):
            nonlocal round_start
            if not calibration or not calibration.get('refresh_x'):
                self.log(f'[打码] 未校准刷新按钮, 无法换题({reason}), 停调等变精灵')
                return False
            x, y = self._calibration_point(calibration['refresh_x'] + calibration.get('refresh_w', 0) / 2, calibration['refresh_y'] + calibration.get('refresh_h', 0) / 2, full.shape, window_rect, window_frame)
            target = (x + self._offx, y + self._offy) if window_frame else (x, y)
            self.dd.move_to(*target)
            time.sleep(0.3)
            self.dd.ml_d()
            self.log(f'[打码] {reason} → 点刷新换题 ({x},{y})')
            failed_answers.clear()
            round_start = time.time()
            self._round_t0 = round_start
            return not self._wait(1.5 + random.uniform(0, 1))
        for retry in range(max_attempts):
            if self._cancel.is_set():
                self.log('[打码] 已按兜底中断退出')
                return None
            if time_left() <= refresh_ahead:
                self.log(f'[打码] 第{retry + 1}次尝试后窗口仅剩{refresh_ahead:.0f}s, 停止试错留时间刷新')
                break
            stage = 'start'
            try:
                full, window_frame, window_rect = self._capture_frame()
                if full is None:
                    raise RuntimeError('截图失败')
                stage = 'crop_captcha'
                roi, dialog_box = self._locate_dialog(full, yolo_rects, calibration, window_rect, window_frame)
                if roi is None or dialog_box is None or roi.size == 0:
                    update_ai_state(status='等待验证码', box=None)
                    return None
                x1, y1, x2, y2 = dialog_box
                update_ai_state(status='检测到弹窗', box=(x1, y1, x2, y2), step=f'裁剪 {x2 - x1}x{y2 - y1}', inc_count_detect=1)
                if not yolo_rects:
                    try:
                        from captcha_ai import is_captcha
                        if is_captcha(roi, 0.6) is False:
                            self.log('[打码] AI判定非验证码, 放行恢复挂机(不消耗机会)')
                            update_ai_state(status='等待验证码', box=None)
                            return None
                    except Exception:
                        pass
                if retry == 0 and alert:
                    self._speak('检测到验证码')
                if self.float_blink:
                    self.float_blink('验证码识别中', '#FF9800')
                update_ai_state(status='识别中', step='运行识别模型')
                stage = 'recognize'
                answer, source, _confidence, error = self._recognize(full, roi, dialog_box, client, local_allowed=local_enabled and local_failures < 3)
                if not answer:
                    self.log(f'[打码] OCR失败: {error}')
                    if any((keyword in error for keyword in ('连接', '网络', '超时', 'Errno', 'Timeout', 'timeout'))):
                        environment_fault = True
                    if self._wait(0.8 + random.uniform(0, 0.8)):
                        return None
                    continue
                if answer in failed_answers:
                    if source == 'local':
                        local_failures += 1
                        self.log(f'[打码] 本地同码识别错(第{local_failures}/3次), ' + ('换手: 老师答同一题' if local_failures >= 3 else '换题再试'))
                    else:
                        cloud_failures += 1
                        self.log(f'[打码] 冰拓答案 {answer} 错(第{cloud_failures}/3次), 换题再试')
                    if local_failures >= 3 and client is None:
                        break
                    if cloud_failures >= 3:
                        break
                    if not refresh_now('答错换题', full, window_rect, window_frame):
                        break
                    continue
                if not auto_submit:
                    self.log(f'[打码] 已识别答案 {answer}, 自动提交已关闭, 等待手动处理')
                    update_ai_state(status='已识别', step='等待手动输入')
                    self._round_ok = True
                    self._session_cd_until = time.time() + 20
                    return None
                stage = 'input'
                foreground_ok, new_rect = self._activate_bound_window()
                if not foreground_ok:
                    continue
                if new_rect:
                    window_rect = new_rect
                input_x, input_y, confirm_x, confirm_y = self._locate_controls(full, dialog_box, yolo_rects, calibration, window_rect, window_frame)
                self.log(f'[打码] 输入→({input_x},{input_y}) 确认→({confirm_x},{confirm_y})')
                if not self._paste_and_submit(answer, input_x, input_y, confirm_x, confirm_y, window_frame):
                    continue
                update_ai_state(status='已输入', step=f'答案 {answer} 已提交')
                stage = 'verify'
                still_visible, last_dialog = self._dialog_still_visible(dialog_box, window_frame)
                if still_visible is None:
                    return None
                if still_visible:
                    failed_answers.append(answer)
                    self._save_rejected(
                        roi, answer, source,
                        datetime.now().strftime('%Y-%m-%d %H:%M:%S.%f')[:-3],
                        _confidence,
                    )
                    raw_answer = getattr(self, '_last_raw_answer', answer)
                    if source == 'local' and len(raw_answer) == len(answer):
                        for raw_char, corrected_char in zip(raw_answer, answer):
                            if raw_char != corrected_char:
                                self._confusion_penalize(raw_char, corrected_char)
                    try:
                        for key in getattr(self, '_applied_shared', set()):
                            self._veto_shared(key, roi)
                        self._applied_shared = set()
                    except Exception:
                        pass
                    self.log('[打码] 弹窗仍在(答案未通过)')
                    if source == 'local':
                        local_failures += 1
                        self.log(f'[打码] 本地答案 {answer} 错(第{local_failures}/3次)')
                    else:
                        cloud_failures += 1
                        self.log(f'[打码] 冰拓答案 {answer} 错(第{cloud_failures}/3次)')
                    self._wipe_input(input_x, input_y, window_frame)
                    if local_failures >= 3 and client is None or cloud_failures >= 3:
                        break
                    if not refresh_now('答错换题', full, window_rect, window_frame):
                        break
                    continue
                if time_left() <= 0:
                    self.log('[打码] 弹窗消失但本轮50s窗口已过, 疑似超时变身, 不判成功, 停止操作')
                    if self.transform_cb:
                        self.transform_cb()
                    return None
                if failed_answers and answer != failed_answers[-1]:
                    self._learn_confusion(failed_answers[-1], answer, roi)
                exhausted = False
                timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S.%f')[:-3]
                self._save_and_clean(roi, 'crop', f'captcha-crop_{answer}', timestamp)
                self._upload_sample_now()
                self.log(f'[打码] 完成 → {answer}')
                update_ai_state(status='验证通过 ✓', step=f'答案 {answer} 正确, 弹窗已消失')
                self._round_ok = True
                return None
            except Exception as exc:
                self.log(f'[验证码异常] 阶段={stage} {exc}')
                if retry < max_attempts - 1:
                    if self._wait(2 + random.uniform(0, 1)):
                        return None
                    continue
                environment_fault = True
        if exhausted:
            self._session_cd_until = time.time() + 90
            if environment_fault:
                self.log(f'[打码] 环境异常达重试上限({max_attempts}次), 停止本轮, 90s后重试')
                if self.float_blink:
                    try:
                        self.float_blink('打码环境异常, 稍后重试', '#f87171')
                    except Exception:
                        pass
            else:
                self.log(f'[打码] 机会(徒弟3+老师3)用尽/窗口耗尽({round_seconds:.0f}s), 停手等变精灵（变精灵后最长20分钟自动解除，期间不做任何操作）')
                if self.transform_cb:
                    try:
                        self.transform_cb()
                    except Exception:
                        pass
                if self.float_blink:
                    try:
                        self.float_blink('验证码未过, 停止操作', '#f87171')
                    except Exception:
                        pass
            if self.fail_cb:
                try:
                    self.fail_cb(last_dialog)
                except Exception:
                    pass

    def _save_and_clean(self, arr, subdir, prefix, ts):
        try:
            from ke_engine import SHOT_DIR
            folder = os.path.join(SHOT_DIR, subdir)
            os.makedirs(folder, exist_ok=True)
            protected = {'crop', 'normal', 'uploaded', 'manual'}
            if subdir not in protected:
                files = sorted(glob.glob(os.path.join(folder, '*.png')), key=os.path.getmtime)
                while len(files) >= 200:
                    os.remove(files.pop(0))
            safe_prefix = re.sub('[\\\\/:*?"<>|]', '_', prefix)
            safe_timestamp = ts.replace(':', '').replace(' ', '_')
            filename = os.path.join(folder, f'{safe_prefix}_{safe_timestamp}.png')
            image = arr[:, :, ::-1] if len(arr.shape) == 3 else arr
            Image.fromarray(image).save(filename, format='PNG')
            return filename
        except Exception as exc:
            try:
                self.log(f'[打码] 样本落盘失败({prefix}): {exc}')
            except Exception:
                pass
            return ''

    def _wipe_input(self, ix, iy, _win_frame):
        if not ix or not iy:
            return None
        try:
            for _ in range(2):
                point = (ix + self._offx, iy + self._offy) if _win_frame else (ix, iy)
                self.dd.move_to(*point)
                time.sleep(random.uniform(0.4, 0.7))
                self.dd.ml_d()
                time.sleep(random.uniform(0.2, 0.4))
                self.dd.ml_u()
            self.dd.kd('ctrl')
            self.dd.kd('a')
            self.dd.ku('a')
            self.dd.ku('ctrl')
            time.sleep(random.uniform(0.2, 0.4))
            self.dd.kd('backspace')
            self.dd.ku('backspace')
            time.sleep(random.uniform(0.3, 0.5))
        except Exception:
            pass

    def _save_rejected(self, arr, code, src, ts, conf=0.0):
        try:
            from ke_engine import SHOT_DIR
            folder = os.path.join(SHOT_DIR, 'rejected')
            os.makedirs(folder, exist_ok=True)
            digest = hashlib.md5(arr.tobytes()).hexdigest()[:12]
            filename = os.path.join(folder, f'captcha-rej_{digest}_{src}.png')
            if not os.path.exists(filename):
                image = arr[:, :, ::-1] if len(arr.shape) == 3 else arr
                Image.fromarray(image).save(filename, format='PNG')
            record = {
                'ts': ts, 'file': os.path.basename(filename), 'src': src,
                'ans': code, 'conf': conf,
            }
            with open(os.path.join(folder, 'rejected.jsonl'), 'a', encoding='utf-8') as stream:
                stream.write(json.dumps(record, ensure_ascii=False) + '\n')
        except Exception as exc:
            try:
                self.log(f'[打码] 被拒样本落盘失败: {exc}')
            except Exception:
                pass

    @staticmethod
    def _sys_keys(seq):
        try:
            user32 = ctypes.windll.user32
            user32.keybd_event.argtypes = [
                ctypes.c_ubyte, ctypes.c_ubyte, ctypes.c_ulong, ctypes.c_ulong,
            ]
            key_map = {
                'ctrl': 17, 'shift': 16, 'alt': 18, 'a': 65, 'v': 86,
                'c': 67, 'x': 88, 'backspace': 8, 'delete': 46,
                'enter': 13,
            }
            keys = [key_map.get(str(key).lower(), 0) for key in seq]
            keys = [key for key in keys if key]
            for key in keys:
                user32.keybd_event(key, 0, 0, 0)
            for key in reversed(keys):
                user32.keybd_event(key, 0, 2, 0)
            return True
        except Exception:
            return False

    @staticmethod
    def _read_edit(hwnd):
        try:
            user32 = ctypes.windll.user32
            user32.SendMessageW.argtypes = [
                wintypes.HWND, wintypes.UINT, wintypes.WPARAM, wintypes.LPARAM,
            ]
            user32.SendMessageW.restype = ctypes.c_ssize_t
            length = user32.SendMessageW(hwnd, 14, 0, 0)
            if length <= 0:
                return ''
            buffer = ctypes.create_unicode_buffer(int(length) + 1)
            user32.SendMessageW(
                hwnd, 13, int(length) + 1,
                ctypes.cast(buffer, ctypes.c_void_p),
            )
            return buffer.value
        except Exception:
            return None

    def _data_dir(self):
        try:
            from DD import SCRIPT_DIR as data_dir
            return data_dir
        except Exception:
            return os.path.dirname(os.path.abspath(__file__))

    def _ke_hidden_dir(self):
        base = self._data_dir()
        directory = os.path.join(base, '.ke')
        try:
            if not os.path.isdir(directory):
                os.makedirs(directory, exist_ok=True)
                _set_attr(directory, 0x02)
            for name in ('混淆纠正表.json', '拉黑表.json', '共享纠正表.json'):
                old_path = os.path.join(base, name)
                new_path = os.path.join(directory, name)
                if os.path.exists(old_path) and not os.path.exists(new_path):
                    try:
                        _unhide_file(old_path)
                        import shutil
                        shutil.move(old_path, new_path)
                    except Exception:
                        pass
            old_events = os.path.join(base, '共享事件')
            new_events = os.path.join(directory, '共享事件')
            if os.path.isdir(old_events) and not os.path.isdir(new_events):
                try:
                    import shutil
                    shutil.move(old_events, new_events)
                except Exception:
                    pass
        except Exception:
            pass
        return directory

    @property
    def _confusion_file(self):
        return os.path.join(self._ke_hidden_dir(), '混淆纠正表.json')

    def _migrate_confusion_file(self):
        try:
            new_path = self._confusion_file
            old_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), '混淆纠正表.json')
            if old_path != new_path and os.path.exists(old_path) and (not os.path.exists(new_path)):
                import shutil
                shutil.copy2(old_path, new_path)
        except Exception:
            pass

    def _confusion_load(self):
        try:
            self._migrate_confusion_file()
            if os.path.exists(self._confusion_file):
                with open(self._confusion_file, 'r', encoding='utf-8') as stream:
                    return json.load(stream)
        except Exception:
            pass
        return {}

    def _confusion_save(self, table):
        try:
            _unhide_file(self._confusion_file)
            temporary = self._confusion_file + '.tmp'
            with open(temporary, 'w', encoding='utf-8') as stream:
                json.dump(table, stream, ensure_ascii=False)
            os.replace(temporary, self._confusion_file)
            _hide_file(self._confusion_file)
        except Exception as exc:
            try:
                self.log(f'[打码] 混淆表保存失败: {exc}')
            except Exception:
                pass

    def _img_to_jpeg_b64(self, arr):
        if arr is None or not hasattr(arr, 'shape') or arr.size == 0:
            return None
        try:
            image = Image.fromarray(arr[:, :, ::-1]) if len(arr.shape) == 3 else Image.fromarray(arr)
            width, height = image.size
            if width > 420:
                image = image.resize((420, max(1, int(height * 420 / width))), Image.LANCZOS)
            stream = io.BytesIO()
            image.convert('RGB').save(stream, format='JPEG', quality=72)
            encoded = base64.b64encode(stream.getvalue()).decode('ascii')
            return encoded if len(encoded) <= 204800 else None
        except Exception:
            return None

    def _learn_confusion(self, fail_ans, ok_ans, img=None):
        if not fail_ans or not ok_ans or len(fail_ans) != len(ok_ans):
            return None
        table = self._confusion_load()
        changed = False
        for failed, correct in zip(fail_ans, ok_ans):
            if failed != correct:
                key = f'{failed}->{correct}'
                before = table.get(key, 0)
                table[key] = before + 1
                changed = True
                if before == 0:
                    self._enqueue_share_event(failed, correct, before + 1, img=img)
        if changed:
            if len(table) > 500:
                for key in sorted(table, key=table.get)[:len(table) - 500]:
                    del table[key]
            self._confusion_save(table)

    def _enqueue_share_event(self, f, o, n, veto=False, img=None):
        try:
            import uuid
            directory = os.path.join(self._ke_hidden_dir(), '共享事件')
            os.makedirs(directory, exist_ok=True)
            _hide_file(directory)
            event = {'f': f, 'o': o, 'n': n, 'ts': time.strftime('%Y%m%d%H%M%S')}
            if veto:
                event['veto'] = 1
            if img is not None:
                encoded = self._img_to_jpeg_b64(img)
                if encoded:
                    event['img'] = encoded
            path = os.path.join(directory, 'evt_%s.json' % uuid.uuid4().hex[:12])
            with open(path, 'w', encoding='utf-8') as stream:
                json.dump(event, stream, ensure_ascii=False)
            _hide_file(path)
            self._upload_events_now()
        except Exception:
            pass

    def _upload_events_now(self):
        if getattr(self, '_evt_uploading', False):
            return None
        self._evt_uploading = True

        def upload():
            try:
                import ke_collect
                settings = self.settings or {}
                base = self._data_dir()
                key = (settings.get('activate_key') or '').strip()
                hwid = settings.get('activate_hwid') or ''
                if not hwid:
                    try:
                        from ke_engine import stable_hwid
                        hwid = stable_hwid()
                    except Exception:
                        pass
                ke_collect._upload_events(base, key, hwid)
            except Exception:
                pass
            finally:
                self._evt_uploading = False
        try:
            threading.Thread(target=upload, daemon=True).start()
        except Exception:
            self._evt_uploading = False

    def _upload_sample_now(self):
        if getattr(self, '_sample_uploading', False):
            return None
        self._sample_uploading = True

        def upload():
            try:
                import ke_collect
                settings = self.settings or {}
                base = self._data_dir()
                key = (settings.get('activate_key') or '').strip()
                hwid = settings.get('activate_hwid') or ''
                if not hwid:
                    try:
                        from ke_engine import stable_hwid
                        hwid = stable_hwid()
                    except Exception:
                        pass
                if key:
                    ke_collect.upload_once(base, key, hwid)
            except Exception:
                pass
            finally:
                self._sample_uploading = False
        try:
            threading.Thread(target=upload, daemon=True).start()
        except Exception:
            self._sample_uploading = False

    def _shared_table_load(self):
        try:
            path = os.path.join(self._ke_hidden_dir(), '共享纠正表.json')
            if os.path.exists(path):
                with open(path, 'r', encoding='utf-8') as stream:
                    return json.load(stream)
        except Exception:
            pass
        return {}

    @property
    def _blacklist_file(self):
        return os.path.join(self._ke_hidden_dir(), '拉黑表.json')

    def _blacklist_load(self):
        try:
            if os.path.exists(self._blacklist_file):
                with open(self._blacklist_file, 'r', encoding='utf-8') as stream:
                    return json.load(stream)
        except Exception:
            pass
        return {}

    def _veto_shared(self, k, img=None):
        try:
            table = self._blacklist_load()
            table[k] = table.get(k, 0) + 1
            _unhide_file(self._blacklist_file)
            temporary = self._blacklist_file + '.tmp'
            with open(temporary, 'w', encoding='utf-8') as stream:
                json.dump(table, stream, ensure_ascii=False)
            os.replace(temporary, self._blacklist_file)
            _hide_file(self._blacklist_file)
            self._enqueue_share_event(k[0], k[3], 1, veto=True, img=img)
        except Exception:
            pass

    def _apply_confusion(self, code):
        table = self._confusion_load()
        if not code:
            return None
        shared = self._shared_table_load()
        blacklist = self._blacklist_load()
        self._applied_shared = set()
        output = list(code)
        for index, character in enumerate(output):
            candidates = {key: count for key, count in table.items() if key[0] == character and key[3] != character}
            for key in list(candidates):
                if f'{key[3]}->{character}' in table or blacklist.get(key, 0) >= 1:
                    del candidates[key]
            corrected = None
            if candidates:
                best_key, best_count = max(candidates.items(), key=lambda item: item[1])
                total = sum(candidates.values())
                if best_count >= 5 and best_count / total >= 0.6:
                    corrected = best_key[3]
            if corrected is None and shared:
                shared_candidates = {key: count for key, count in shared.items() if key[0] == character and key[3] != character}
                for key in list(shared_candidates):
                    if blacklist.get(key, 0) >= 2 or f'{key[3]}->{character}' in table:
                        del shared_candidates[key]
                if shared_candidates:
                    best_key = max(shared_candidates, key=lambda key: shared_candidates[key])
                    corrected = best_key[3]
                    self._applied_shared.add(best_key)
            if corrected is not None:
                output[index] = corrected
        result = ''.join(output)
        return result if result != code else None

    def _confusion_blacklisted(self, raw, corrected):
        try:
            return self._blacklist_load().get(f'{raw}->{corrected}', 0) >= 1
        except Exception:
            return False

    def _confusion_penalize(self, raw, corrected):
        if not raw or not corrected or raw == corrected:
            return None
        key = f'{raw}->{corrected}'
        try:
            table = self._confusion_load()
            if key in table:
                table[key] -= 3
                if table[key] <= 0:
                    del table[key]
                self._confusion_save(table)
            blacklist = self._blacklist_load()
            blacklist[key] = blacklist.get(key, 0) + 1
            _unhide_file(self._blacklist_file)
            temporary = self._blacklist_file + '.tmp'
            with open(temporary, 'w', encoding='utf-8') as stream:
                json.dump(blacklist, stream, ensure_ascii=False)
            os.replace(temporary, self._blacklist_file)
            self.log(f'[打码] 纠正 {key} 被游戏拒绝, 配对降票并拉黑')
        except Exception:
            return None

    def _speak(self, text):
        if _tts_func:
            try:
                _tts_func(text)
            except Exception:
                pass

def create_solver(dd, settings, log_cb=None, float_cb=None):
    return CaptchaSolver(dd, settings, log_cb, float_cb)

def check_bingtop_points(username, password, captcha_type='1017'):
    client = BingtopClient(username, password, captcha_type)
    return client.check_points()
