"""KE Driver、输入引擎、DXGI 截图、OCR 和 Lua 脚本运行时。"""
from __future__ import annotations
import asyncio
import base64
import ctypes
from ctypes import wintypes
import hashlib
import json
import os
import random
import re
import shutil
import sys
import threading
import time
import cv2
import dxcam
import numpy as np
from PIL import Image, ImageDraw, ImageTk
import tkinter as tk
from tkinter import filedialog, messagebox, scrolledtext, ttk
import win32api
import win32con
import win32gui
import win32ui
from captcha_service import CaptchaSolver, BingtopClient, set_tts_callback
from ke_ai import ocr_correct_angle, ocr_detect_text
from ke_mem import KeMem, _err_text as _mem_err_text
from quick_recognition import QuickRecognition
try:
    if sys.executable.endswith('python.exe'):
        ctypes.windll.user32.ShowWindow(ctypes.windll.kernel32.GetConsoleWindow(), 0)
except Exception:
    pass
_mem_viz = {'connected': False, 'pid': 0, 'bits': 0, 'err': '', 'attach': '', 'rules': {}}
_mem_viz_lock = threading.Lock()

def get_mem_viz():
    try:
        import copy
        with _mem_viz_lock:
            return copy.deepcopy(_mem_viz)
    except Exception:
        return dict(_mem_viz)

def eval_expect(value, expect):
    if expect is None:
        return True
    if 'nonzero' in expect:
        return bool(value)
    if 'value' in expect:
        expected = expect['value']
        operation = expect.get('op', '==')
        if operation == '==':
            return value == expected
        if operation == '!=':
            return value != expected
        if operation == '>':
            return value > expected
        if operation == '<':
            return value < expected
        if operation == '>=':
            return value >= expected
        if operation == '<=':
            return value <= expected
        return False
    if 'range' in expect:
        lower, upper = expect['range']
        return lower <= value <= upper
    return False
DEFAULT_TOLERANCE = 30
DEFAULT_TOL = 30
FRAME_CACHE_INTERVAL = 0.01
CLICK_PRE_DELAY = 0.001
OCR_MODES = {'数字': ('eng', '-c tessedit_char_whitelist=0123456789'), 'number': ('eng', '-c tessedit_char_whitelist=0123456789'), '英文': ('eng', '-c tessedit_char_whitelist=ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789'), 'eng': ('eng', '-c tessedit_char_whitelist=ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789'), '中文': ('chi_sim+chi_tra', ''), 'chi': ('chi_sim+chi_tra', '')}
OCR_PSM_ORDER = [7, 8, 6]
_BINGTOP_CREDS = None
_BINGTOP_LAST_LOAD = 0
if getattr(sys, '_MEIPASS', None):
    SCRIPT_DIR = os.path.dirname(os.path.abspath(sys.argv[0]))
else:
    SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
SCRIPTS_DIR = os.path.join(SCRIPT_DIR, '驱动')
_OLD_SCRIPTS = os.path.join(SCRIPT_DIR, '脚本')
if not os.path.exists(SCRIPTS_DIR) and os.path.exists(_OLD_SCRIPTS):
    try:
        os.rename(_OLD_SCRIPTS, SCRIPTS_DIR)
    except Exception:
        pass
SETTINGS_FILE = os.path.join(SCRIPT_DIR, '设置.json')
CACHE_SALT = 'KEDrv2026@#xM'
try:
    import atexit
    _winmm = ctypes.windll.winmm
    if _winmm.timeBeginPeriod(1) == 0:
        atexit.register(lambda: _winmm.timeEndPeriod(1))
except Exception:
    pass

def _resolve_shot_dir():
    public_dir = os.path.join(os.environ.get('PUBLIC', 'C:\\Users\\Public'), 'Pictures', 'logs')
    try:
        os.makedirs(public_dir, exist_ok=True)
        return public_dir
    except Exception:
        pass
    home_dir = os.path.join(os.path.expanduser('~'), 'KE外设验证码截图')
    try:
        os.makedirs(home_dir, exist_ok=True)
        return home_dir
    except Exception:
        return os.path.join(SCRIPT_DIR, 'logs', 'img')
SHOT_DIR = _resolve_shot_dir()
_AI_TRAIN_STATE = {'last_ts': 0, 'acc': 0.0, 'pos': 0, 'neg': 0, 'msg': ''}
_LUA_MAGIC = b'KELUA01'
_KM_DLL = None


def _km_find():
    candidates = (
        getattr(sys, '_MEIPASS', None),
        os.path.dirname(sys.executable),
        SCRIPT_DIR,
        os.path.dirname(os.path.abspath(__file__)),
    )
    for base in candidates:
        if base and os.path.isfile(os.path.join(base, 'keymod.dll')):
            return os.path.join(base, 'keymod.dll')
    return None

def _lua_key():
    return _km('lua')

def lua_encrypt(text):
    try:
        from Crypto.Cipher import AES
        from Crypto.Util.Padding import pad
        iv = os.urandom(16)
        encrypted = AES.new(_lua_key(), AES.MODE_CBC, iv).encrypt(pad(text.encode('utf-8'), 16))
        return _LUA_MAGIC + iv + encrypted
    except Exception:
        return text.encode('utf-8')

def lua_decrypt(data):
    if isinstance(data, str):
        return data
    if data[:len(_LUA_MAGIC)] == _LUA_MAGIC:
        try:
            from Crypto.Cipher import AES
            from Crypto.Util.Padding import unpad
            iv = data[len(_LUA_MAGIC):len(_LUA_MAGIC) + 16]
            encrypted = data[len(_LUA_MAGIC) + 16:]
            return unpad(AES.new(_lua_key(), AES.MODE_CBC, iv).decrypt(encrypted), 16).decode('utf-8')
        except Exception:
            return ''
    return data.decode('utf-8', errors='replace')

def lua_read_text(path):
    with open(path, 'rb') as stream:
        return lua_decrypt(stream.read())

def lua_write_text(path, text):
    encrypted = False
    if os.path.exists(path):
        try:
            with open(path, 'rb') as stream:
                encrypted = stream.read(len(_LUA_MAGIC)) == _LUA_MAGIC
        except Exception:
            pass
    if encrypted:
        with open(path, 'wb') as stream:
            stream.write(lua_encrypt(text))
    else:
        with open(path, 'w', encoding='utf-8') as stream:
            stream.write(text)

def _first_run_init():
    os.makedirs(SCRIPTS_DIR, exist_ok=True)
    for subdir in ('图库', '色库', '文库', 'logs'):
        try:
            os.makedirs(os.path.join(SCRIPT_DIR, subdir), exist_ok=True)
        except Exception:
            pass
    for subdir in ('crop', 'full', 'normal', 'manual', 'uploaded'):
        try:
            os.makedirs(os.path.join(SHOT_DIR, subdir), exist_ok=True)
        except Exception:
            pass
    packaged = getattr(sys, '_MEIPASS', None)
    if not packaged:
        return
    resources = (('设置.json', SETTINGS_FILE), ('icon_pink.ico', os.path.join(SCRIPT_DIR, 'icon_pink.ico')), ('ke_active.ico', os.path.join(SCRIPT_DIR, 'ke_active.ico')), ('DD64.dll', os.path.join(SCRIPT_DIR, 'DD64.dll')), ('DDHID64.dll', os.path.join(SCRIPT_DIR, 'DDHID64.dll')), ('F.dll', os.path.join(SCRIPT_DIR, 'F.dll')), ('captcha_model.pkl', os.path.join(SCRIPT_DIR, 'captcha_model.pkl')), ('captcha_model.xml', os.path.join(SCRIPT_DIR, 'captcha_model.xml')))
    for filename, destination in resources:
        try:
            source = os.path.join(packaged, filename)
            if os.path.exists(source) and (not os.path.exists(destination)):
                shutil.copy2(source, destination)
        except Exception:
            pass
    for dirname in ('tessdata', 'models'):
        try:
            source = os.path.join(packaged, dirname)
            destination = os.path.join(SCRIPT_DIR, dirname)
            if os.path.isdir(source) and (not os.path.isdir(destination)):
                shutil.copytree(source, destination)
        except Exception:
            pass
    try:
        driver_source = os.path.join(packaged, '驱动')
        if os.path.isdir(driver_source):
            for filename in os.listdir(driver_source):
                source = os.path.join(driver_source, filename)
                destination = os.path.join(SCRIPTS_DIR, filename)
                if os.path.isfile(source) and (not os.path.exists(destination)):
                    shutil.copy2(source, destination)
    except Exception:
        pass
_first_run_init()
DEFAULT_SETTINGS = {'hotkey_start': 'Home', 'input_mode': 'ttinput', 'theme': '原始粉', 'voice': True, 'fix_delay_ms': '30', 'config_version': 1, 'float_show': True, 'float_size': 17}
TRANSFORM_CD_SECONDS = 1200
THEMES = {
    name: {
        **values,
        'list_bg': '#262626',
        'list_fg': '#d6d2ca',
        'list_sel': '#3a3a3a',
        'list_sel_fg': '#ffffff',
        'head_bg': '#262626',
        'head_fg': '#e6edf3',
        'head_hover': '#353535',
        'gp_bg': '#2f2f2f',
        'gp_fg': '#cccccc',
    }
    for name, values in {
        '原始粉': {'bg': '#f0f0f0', 'card': '#ffffff', 'accent': '#E91E63', 'text': '#222', 'sub': '#888', 'tag': '#ccc', 'btn_bg': '#E91E63', 'btn_fg': 'white', 'log_bg': '#161b22', 'log_fg': '#ccc'},
        '初音': {'bg': '#e8f5e9', 'card': '#ffffff', 'accent': '#66bb6a', 'text': '#263238', 'sub': '#78909c', 'tag': '#c8e6c9', 'btn_bg': '#66bb6a', 'btn_fg': 'white', 'log_bg': '#263238', 'log_fg': '#a5d6a7'},
        '桃粉': {'bg': '#fce4ec', 'card': '#fff0f5', 'accent': '#E91E63', 'text': '#311b1b', 'sub': '#9e7777', 'tag': '#f8bbd0', 'btn_bg': '#E91E63', 'btn_fg': 'white', 'log_bg': '#2d1f24', 'log_fg': '#f48fb1'},
        '暗夜': {'bg': '#1a1a2e', 'card': '#1e2840', 'accent': '#e94560', 'text': '#d4d8e0', 'sub': '#8899aa', 'tag': '#556677', 'btn_bg': '#e94560', 'btn_fg': 'white', 'log_bg': '#0d1117', 'log_fg': '#c9d1d9'},
        '极墨': {'bg': '#202020', 'card': '#2b2b2b', 'accent': '#58a6ff', 'text': '#f2f2f2', 'sub': '#9d9d9d', 'tag': '#3a3a3a', 'btn_bg': '#238636', 'btn_fg': 'white', 'log_bg': '#2b2b2b', 'log_fg': '#d0d0d0'},
        '尊贵紫': {'bg': '#1a1025', 'card': '#241a33', 'accent': '#ab47bc', 'text': '#d1c4e0', 'sub': '#9575a8', 'tag': '#4a3060', 'btn_bg': '#8e24aa', 'btn_fg': 'white', 'log_bg': '#0d0814', 'log_fg': '#ce93d8'},
        '日落': {'bg': '#2d1b14', 'card': '#3e261a', 'accent': '#ff7043', 'text': '#e8cfc0', 'sub': '#b0856b', 'tag': '#5d3a28', 'btn_bg': '#ff7043', 'btn_fg': '#2d1b14', 'log_bg': '#1a0f0a', 'log_fg': '#ffab91'},
        '蔚蓝': {'bg': '#0f1b2d', 'card': '#162840', 'accent': '#4da6ff', 'text': '#c8daf0', 'sub': '#7a9fc0', 'tag': '#2a4a6a', 'btn_bg': '#4da6ff', 'btn_fg': 'white', 'log_bg': '#0a1420', 'log_fg': '#a0c8f0'},
    }.items()
}
VK_MAP = {f'F{index}': 111 + index for index in range(1, 13)}
VK_MAP.update({'Home': 36, 'End': 35, 'Insert': 45, 'Delete': 46, 'PageUp': 33, 'PageDown': 34, 'Scroll': 145, 'Pause': 19})
DD_KEY = {'esc': 1, '1': 2, '2': 3, '3': 4, '4': 5, '5': 6, '6': 7, '7': 8, '8': 9, '9': 10, '0': 11, '-': 12, '=': 13, 'backspace': 14, 'tab': 15, 'q': 16, 'w': 17, 'e': 18, 'r': 19, 't': 20, 'y': 21, 'u': 22, 'i': 23, 'o': 24, 'p': 25, '[': 26, ']': 27, 'enter': 28, 'lctrl': 29, 'ctrl': 29, 'a': 30, 's': 31, 'd': 32, 'f': 33, 'g': 34, 'h': 35, 'j': 36, 'k': 37, 'l': 38, ';': 39, "'": 40, '`': 41, 'lshift': 42, 'shift': 42, '\\': 43, 'z': 44, 'x': 45, 'c': 46, 'v': 47, 'b': 48, 'n': 49, 'm': 50, ',': 51, '.': 52, '/': 53, 'space': 57, 'capslock': 58, 'f1': 59, 'f2': 60, 'f3': 61, 'f4': 62, 'f5': 63, 'f6': 64, 'f7': 65, 'f8': 66, 'f9': 67, 'f10': 68, 'f11': 69, 'f12': 70}
DD_VK = {'esc': 27, '1': 49, '2': 50, '3': 51, '4': 52, '5': 53, '6': 54, '7': 55, '8': 56, '9': 57, '0': 48, '-': 189, '=': 187, 'backspace': 8, 'tab': 9, 'q': 81, 'w': 87, 'e': 69, 'r': 82, 't': 84, 'y': 89, 'u': 85, 'i': 73, 'o': 79, 'p': 80, '[': 219, ']': 221, 'enter': 13, 'lctrl': 17, 'ctrl': 17, 'a': 65, 's': 83, 'd': 68, 'f': 70, 'g': 71, 'h': 72, 'j': 74, 'k': 75, 'l': 76, ';': 186, "'": 222, '`': 192, 'lshift': 16, 'shift': 16, '\\': 220, 'z': 90, 'x': 88, 'c': 67, 'v': 86, 'b': 66, 'n': 78, 'm': 77, ',': 188, '.': 190, '/': 191, 'space': 32, 'capslock': 20, **{f'f{index}': 111 + index for index in range(1, 13)}}
DD_SC = dict(DD_KEY)
DD_SC.update({'f11': 87, 'f12': 88})
_HWID_CACHE = ''
_FP_PLACEHOLDERS = {
    '',
    '0',
    '00000000',
    'none',
    'unknown',
    'default string',
    'not specified',
    'system serial number',
    'to be filled by o.e.m.',
}


def _hw_sns():
    motherboard = ''
    disk = ''
    query = (
        "$o=@{};$o.mb=(Get-CimInstance Win32_BaseBoard -ErrorAction SilentlyContinue | "
        "Select-Object -First 1).SerialNumber;$o.disk=(Get-CimInstance Win32_DiskDrive "
        "-ErrorAction SilentlyContinue | Select-Object -First 1).SerialNumber;"
        "Write-Output ('MB=' + [string]$o.mb);Write-Output ('DSK=' + [string]$o.disk)"
    )
    try:
        import subprocess
        result = subprocess.run(
            ['powershell', '-NoProfile', '-NonInteractive', '-Command', query],
            capture_output=True,
            text=True,
            encoding='gbk',
            errors='replace',
            timeout=8,
            creationflags=0x08000000,
        )
        for line in (result.stdout or '').strip().split('\n'):
            line = line.strip()
            if line.startswith('MB='):
                motherboard = line[3:].strip()
            elif line.startswith('DSK='):
                disk = line[4:].strip()
    except Exception:
        pass
    try:
        import subprocess
        for tag, current in (('mb', motherboard), ('disk', disk)):
            if current:
                continue
            result = subprocess.run(
                ['wmic', 'baseboard' if tag == 'mb' else 'diskdrive', 'get', 'serialnumber'],
                capture_output=True,
                text=True,
                encoding='gbk',
                errors='replace',
                timeout=5,
                creationflags=0x08000000,
            )
            for line in result.stdout.strip().split('\n'):
                line = line.strip()
                if line and 'SerialNumber' not in line and line.lower() not in ('', 'none'):
                    if tag == 'mb':
                        motherboard = line
                    else:
                        disk = line
                    break
    except Exception:
        pass
    return [value for value in (motherboard, disk) if value.lower() not in _FP_PLACEHOLDERS]

def stable_hwid():
    global _HWID_CACHE
    if _HWID_CACHE:
        return _HWID_CACHE
    parts = _hw_sns()
    if parts:
        _HWID_CACHE = hashlib.md5('|'.join(parts).encode()).hexdigest()[slice(None, 12)]
    else:
        _HWID_CACHE = hashlib.md5(os.environ.get('COMPUTERNAME', '').encode()).hexdigest()[slice(None, 12)]
    return _HWID_CACHE


_LEGACY_CACHE = ''


def _legacy_read():
    value = load_settings().get('legacy_hwid', '')
    if len(value) == 12:
        return value
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, r'Software\KEMouse') as key:
            value = winreg.QueryValueEx(key, 'legacy_hwid')[0]
            if len(value) == 12:
                return value
    except Exception:
        pass
    return ''


def _legacy_save(value):
    settings = load_settings()
    settings['legacy_hwid'] = value
    save_settings(settings)
    try:
        import winreg
        with winreg.CreateKey(winreg.HKEY_CURRENT_USER, r'Software\KEMouse') as key:
            winreg.SetValueEx(key, 'legacy_hwid', 0, winreg.REG_SZ, value)
    except Exception:
        pass


_SETTINGS_CACHE = {'mtime': None, 'data': None}

def load_settings():
    if os.path.exists(SETTINGS_FILE):
        try:
            with open(SETTINGS_FILE, 'r', encoding='utf-8') as stream:
                settings = json.load(stream)
            if not isinstance(settings, dict):
                print('[DD.load_settings] 设置.json顶层非对象, 已改名 .bad 留证')
                try:
                    os.replace(SETTINGS_FILE, SETTINGS_FILE + '.bad')
                except Exception:
                    pass
                return dict(DEFAULT_SETTINGS)
            try:
                for key, default in DEFAULT_SETTINGS.items():
                    if key not in settings:
                        settings[key] = default
                        continue
                    value = settings[key]
                    expected_type = type(default)
                    if expected_type is bool:
                        if not isinstance(value, bool):
                            settings[key] = bool(value) if isinstance(value, int) else default
                    elif expected_type is int:
                        if isinstance(value, bool) or not isinstance(value, int):
                            settings[key] = default
                    elif expected_type is str:
                        if not isinstance(value, str):
                            settings[key] = str(value) if isinstance(value, (int, float)) else default
                    elif not isinstance(value, expected_type):
                        settings[key] = default
            except Exception:
                pass
            if settings.get('bingtop_pwd'):
                try:
                    decoded = base64.b64decode(settings['bingtop_pwd']).decode('utf-8', 'ignore')
                    if decoded and len(decoded) <= 64 and all((32 <= ord(char) < 127 for char in decoded)):
                        settings['bingtop_pwd'] = decoded
                except Exception:
                    pass
            if settings.get('config_version', 0) < 1:
                settings['config_version'] = 1
            return settings
        except Exception as exc:
            print(f'[DD.load_settings] {exc}')
            try:
                os.replace(SETTINGS_FILE, SETTINGS_FILE + '.bad')
            except Exception:
                pass
    return dict(DEFAULT_SETTINGS)
_SETTINGS_LOCK = threading.Lock()

def save_settings(settings):
    saved_password = None
    success = True
    with _SETTINGS_LOCK:
        if settings.get('bingtop_pwd'):
            saved_password = settings['bingtop_pwd']
            try:
                settings['bingtop_pwd'] = base64.b64encode(settings['bingtop_pwd'].encode()).decode()
            except Exception:
                pass
        try:
            temporary = SETTINGS_FILE + '.tmp'
            with open(temporary, 'w', encoding='utf-8') as stream:
                json.dump(dict(settings), stream, ensure_ascii=False, indent=2)
            os.replace(temporary, SETTINGS_FILE)
        except Exception as exc:
            print(f'[DD.save_settings] {exc}')
            success = False
        if saved_password is not None:
            settings['bingtop_pwd'] = saved_password
    return success

class _KEYBDINPUT(ctypes.Structure):
    _fields_ = [('wVk', wintypes.WORD), ('wScan', wintypes.WORD), ('dwFlags', wintypes.DWORD), ('time', wintypes.DWORD), ('dwExtraInfo', ctypes.POINTER(ctypes.c_ulong))]

class _INPUT(ctypes.Structure):
    _fields_ = [('type', wintypes.DWORD), ('ki', _KEYBDINPUT)]

class SendInputKB:

    def __init__(self):
        self._user32 = ctypes.windll.user32
        self._VK = {str(index): 48 + index for index in range(10)}
        self._VK.update({chr(65 + index): 65 + index for index in range(26)})
        self._VK.update({'tab': 9, 'enter': 13, 'space': 32, 'esc': 27, 'backspace': 8, 'shift': 16, 'ctrl': 17, 'alt': 18, 'lshift': 160, 'rshift': 161, 'lctrl': 162, 'rctrl': 163, 'lalt': 164, 'ralt': 165, 'up': 38, 'down': 40, 'left': 37, 'right': 39, 'home': 36, 'end': 35, 'insert': 45, 'delete': 46, 'pageup': 33, 'pagedown': 34, 'capslock': 20, **{f'f{index}': 111 + index for index in range(1, 13)}, '=': 187, '-': 189, ',': 188, '.': 190, '/': 191, ';': 186, '[': 219, ']': 221, '`': 192})

    def _vk(self, key):
        return self._VK.get(key.lower(), 0)

    def kd(self, key):
        vk = self._vk(key)
        if vk:
            value = _INPUT(1, _KEYBDINPUT(vk, 0, 0, 0, None))
            self._user32.SendInput(1, ctypes.byref(value), ctypes.sizeof(_INPUT))

    def ku(self, key):
        vk = self._vk(key)
        if vk:
            value = _INPUT(1, _KEYBDINPUT(vk, 0, 2, 0, None))
            self._user32.SendInput(1, ctypes.byref(value), ctypes.sizeof(_INPUT))

    def kp(self, key, ms=50):
        self.kd(key)
        if ms > 0:
            time.sleep(ms / 1000.0)
        self.ku(key)

    def release(self):
        for vk in set(self._VK.values()):
            value = _INPUT(1, _KEYBDINPUT(vk, 0, 2, 0, None))
            self._user32.SendInput(1, ctypes.byref(value), ctypes.sizeof(_INPUT))
_KM_SIGS = {'KmInit': ([], ctypes.c_int), 'KmAuth': ([ctypes.c_char_p], ctypes.c_int), 'KmIsReady': ([], ctypes.c_int), 'KmEnsureReady': ([], ctypes.c_int), 'KmRefresh': ([], ctypes.c_int), 'KmClose': ([], ctypes.c_int), 'KmGetLastErrorCode': ([], ctypes.c_int), 'KmKeyDown': ([ctypes.c_int], ctypes.c_int), 'KmKeyUp': ([ctypes.c_int], ctypes.c_int), 'KmKeyPress': ([ctypes.c_int], ctypes.c_int), 'KmMouseMove': ([ctypes.c_int, ctypes.c_int], ctypes.c_int), 'KmMouseMoveAbsolute': ([ctypes.c_int, ctypes.c_int], ctypes.c_int), 'KmMouseLeftClick': ([], ctypes.c_int), 'KmMouseLeftDown': ([], ctypes.c_int), 'KmMouseLeftUp': ([], ctypes.c_int), 'KmMouseRightClick': ([], ctypes.c_int), 'KmMouseRightDown': ([], ctypes.c_int), 'KmMouseRightUp': ([], ctypes.c_int), 'KmMouseMiddleClick': ([], ctypes.c_int), 'KmMouseMiddleDown': ([], ctypes.c_int), 'KmMouseMiddleUp': ([], ctypes.c_int), 'KmMouseScroll': ([ctypes.c_int], ctypes.c_int)}

class KEDriverInput:
    _AUTH_KEY = b'local-dev'
    _CACHED_INSTANCE = None

    def __init__(self):
        self._AUTH_KEY = os.urandom(16)
        if KEDriverInput._CACHED_INSTANCE is not None:
            _c = KEDriverInput._CACHED_INSTANCE
            self._dll = _c._dll
            self._k32 = _c._k32
            self._km = _c._km
            self._VK = _c._VK
            self._lock = _c._lock
            return None
        _mei = getattr(sys, '_MEIPASS', None)
        if _mei:
            dll_path = os.path.join(_mei, 'ttinput.dll')
        else:
            dll_path = ''
        if dll_path:
            if not os.path.exists(dll_path):
                dll_path = os.path.join(SCRIPT_DIR, 'ttinput.dll')
        else:
            dll_path = os.path.join(SCRIPT_DIR, 'ttinput.dll')
        if not os.path.exists(dll_path):
            raise RuntimeError('驱动文件缺失, 请重新安装软件或重启电脑后重试')
        self._dll = ctypes.WinDLL(dll_path)
        self._lock = threading.RLock()
        self._k32 = ctypes.windll.kernel32
        self._k32.GetProcAddress.restype = ctypes.c_void_p
        self._k32.GetProcAddress.argtypes = [ctypes.c_void_p, ctypes.c_char_p]
        self._km = {}
        for __temp_2277 in iter(_KM_SIGS.items()):
            __temp_2278, __temp_2279 = __temp_2277
            name = __temp_2278
            __temp_2280, __temp_2281 = __temp_2279
            argtypes = __temp_2280
            restype = __temp_2281
            p = self._k32.GetProcAddress(ctypes.c_void_p(self._dll._handle), name.encode())
            if p:
                __temp_2286 = [restype]
                __temp_2286.extend(argtypes)
                self._km[name] = ctypes.WINFUNCTYPE(*tuple(__temp_2286))(p)
            continue
        self._VK = dict(DD_VK)
        self._VK.update({
            'alt': 18, 'rshift': 161, 'lctrl': 162, 'rctrl': 163,
            'lalt': 164, 'ralt': 165, 'up': 38, 'down': 40,
            'left': 37, 'right': 39, 'home': 36, 'end': 35,
            'insert': 45, 'delete': 46, 'pageup': 33, 'pagedown': 34,
        })
        if not self._init_driver():
            raise RuntimeError('KE Driver 驱动未就绪\n\n请重启电脑后重试，若仍失败请重新安装软件')
        KEDriverInput._CACHED_INSTANCE = self
        return None

    def _call(self, name, *args):
        function = self._km.get(name)
        if function is None:
            print(f'[KEDriver] 缺少导出: {name}')
            return 0
        try:
            with self._lock:
                return function(*args)
        except Exception as exc:
            print(f'[KEDriver] {name}{args} 异常: {exc}')
            return 0

    def _init_driver(self):
        try:
            self._call('KmInit')
            time.sleep(0.3)
            self._call('KmAuth', self._AUTH_KEY)
            time.sleep(0.5)
            for _ in range(3):
                if self._call('KmIsReady'):
                    return True
                self._call('KmRefresh')
                time.sleep(0.5)
            print(f"[KEDriver] 驱动未就绪，错误码={self._call('KmGetLastErrorCode')}")
        except Exception as exc:
            print(f'[KEDriver] 初始化异常: {exc}')
        return False

    def kd(self, key):
        vk = self._VK.get(str(key).lower(), 0)
        if vk:
            self._call('KmKeyDown', vk)
        else:
            print(f'[KEDriver] 未知键: {key}')

    def ku(self, key):
        vk = self._VK.get(str(key).lower(), 0)
        if vk:
            self._call('KmKeyUp', vk)

    def kp(self, key, ms=50):
        self.kd(key)
        if ms > 0:
            time.sleep(ms / 1000.0)
        self.ku(key)

    def ml_d(self):
        self._call('KmMouseLeftDown')

    def ml_u(self):
        self._call('KmMouseLeftUp')

    def mr_d(self):
        self._call('KmMouseRightDown')

    def mr_u(self):
        self._call('KmMouseRightUp')

    def mm_d(self):
        self._call('KmMouseMiddleDown')

    def mm_u(self):
        self._call('KmMouseMiddleUp')

    def mm(self, ms=50):
        self.mm_d()
        if ms > 0:
            time.sleep(ms / 1000.0)
        self.mm_u()

    def move_r(self, dx, dy):
        self._call('KmMouseMove', int(dx), int(dy))

    def move_to(self, x, y):
        self._call('KmMouseMoveAbsolute', int(x), int(y))

    def click(self):
        self._call('KmMouseLeftClick')

    def scroll(self, delta):
        self._call('KmMouseScroll', int(delta))

    def release(self):
        try:
            (self.ml_u(), self.mr_u(), self.mm_u())
            for key in list(self._VK):
                self.ku(key)
        except Exception as exc:
            print(f'[KEDriver] release {exc}')

class DDInput:

    def __init__(self):
        self._dd = ctypes.WinDLL(os.path.join(SCRIPT_DIR, 'DD64.dll'))
        self._lock = threading.RLock()
        for name, argtypes in {'DD_btn': [ctypes.c_int], 'DD_mov': [ctypes.c_int, ctypes.c_int], 'DD_movR': [ctypes.c_int, ctypes.c_int], 'DD_whl': [ctypes.c_int], 'DD_key': [ctypes.c_int, ctypes.c_int], 'DD_str': [ctypes.c_char_p]}.items():
            function = getattr(self._dd, name)
            function.argtypes = argtypes
            function.restype = ctypes.c_int
        try:
            self._dd.DD_btn(0)
        except Exception as exc:
            print(f'[DDInput] DD驱动加载失败: {exc}')

    def _scan_code(self, key):
        return DD_KEY.get(key.lower(), 0)

    def _dd_call(self, name, *args):
        with self._lock:
            return getattr(self._dd, name)(*args)

    def kd(self, key):
        code = self._scan_code(key)
        if code:
            self._dd_call('DD_key', code, 1)

    def ku(self, key):
        code = self._scan_code(key)
        if code:
            self._dd_call('DD_key', code, 2)

    def kp(self, key, ms=50):
        self.kd(key)
        if ms > 0:
            time.sleep(ms / 1000.0)
        self.ku(key)

    def ml_d(self):
        self._dd_call('DD_btn', 1)

    def ml_u(self):
        self._dd_call('DD_btn', 2)

    def mr_d(self):
        self._dd_call('DD_btn', 4)

    def mr_u(self):
        self._dd_call('DD_btn', 8)

    def mm_d(self):
        self._dd_call('DD_btn', 16)

    def mm_u(self):
        self._dd_call('DD_btn', 32)

    def move_r(self, dx, dy):
        self._dd_call('DD_movR', int(dx), int(dy))

    def move_to(self, x, y):
        self._dd_call('DD_mov', int(x), int(y))

    def whl(self, delta):
        self._dd_call('DD_whl', int(delta))

    def release(self):
        (self.ml_u(), self.mr_u(), self.mm_u())
        for character in "abcdefghijklmnopqrstuvwxyz0123456789-=[];'#\\,./`":
            code = self._scan_code(character)
            if code:
                self._dd.DD_key(code, 2)
        for key in ('shift', 'ctrl', 'alt', 'tab', 'space', 'enter', 'esc', 'backspace', 'f1', 'f2', 'f3', 'f4', 'f5', 'f6', 'f7', 'f8', 'f9', 'f10', 'f11', 'f12'):
            code = self._scan_code(key)
            if code:
                self._dd.DD_key(code, 2)

def get_tesseract_path():
    paths = ['C:\\Program Files\\Tesseract-OCR\\tesseract.exe', 'C:\\Program Files (x86)\\Tesseract-OCR\\tesseract.exe', 'D:\\下载文件\\Tesseract-OCR\\tesseract.exe']
    found = shutil.which('tesseract')
    if found:
        paths.insert(0, found)
    for path in paths:
        if os.path.exists(path):
            tessdata = os.path.join(os.path.dirname(path), 'tessdata')
            if os.path.isdir(tessdata):
                os.environ['TESSDATA_PREFIX'] = tessdata
            return path
    local = os.path.join(SCRIPT_DIR, 'tessdata', 'tessdata-main')
    if os.path.isdir(local):
        os.environ['TESSDATA_PREFIX'] = local
    return None
_DX_CAM = None
_DX_REF = 0
_DX_EPOCH = 0
_DX_LOCK = threading.Lock()
_MEM_INIT_LOCK = threading.Lock()
_CAM_ERR_LAST = [0.0]

def _log_cam_error(msg):
    now = time.time()
    if now - _CAM_ERR_LAST[0] < 10.0:
        return
    _CAM_ERR_LAST[0] = now
    try:
        with open(os.path.join(SCRIPT_DIR, '日志.txt'), 'a', encoding='utf-8') as stream:
            stream.write(time.strftime('%Y-%m-%d %H:%M:%S') + ' ' + msg + '\n')
    except Exception:
        pass

def dxcam_epoch():
    return _DX_EPOCH

def new_dxcam():
    global _DX_CAM, _DX_REF
    with _DX_LOCK:
        if _DX_CAM is not None:
            _DX_REF += 1
            return _DX_CAM
        try:
            _DX_CAM = dxcam.create(output_color='BGR')
        except Exception:
            try:
                _DX_CAM = dxcam.create()
            except Exception as exc:
                print(f'[_new_dxcam] {exc}')
                _DX_CAM = None
                return None
        _DX_REF += 1
        return _DX_CAM

def release_dxcam(cam):
    global _DX_REF
    if cam is None:
        return
    with _DX_LOCK:
        if cam is not _DX_CAM:
            try:
                cam.stop()
            except Exception:
                pass
            return
        _DX_REF -= 1
        if _DX_REF <= 0:
            _DX_REF = 0

def reset_dxcam():
    global _DX_CAM, _DX_REF, _DX_EPOCH
    with _DX_LOCK:
        if _DX_CAM is not None:
            try:
                _DX_CAM.release()
            except Exception:
                pass
        _DX_CAM = None
        _DX_REF = 0
        _DX_EPOCH += 1

def _restore_offscreen(hwnd):
    try:
        if not win32gui.IsIconic(hwnd):
            return False
        foreground = win32gui.GetForegroundWindow()
        win32gui.ShowWindow(hwnd, 4)
        time.sleep(0.15)
        rect = win32gui.GetWindowRect(hwnd)
        width, height = (rect[2] - rect[0], rect[3] - rect[1])
        if width <= 0 or height <= 0:
            return False
        ctypes.windll.user32.SetWindowPos(hwnd, 0, -32000, -32000, width, height, 20)
        if foreground and foreground != hwnd and (win32gui.GetForegroundWindow() == hwnd):
            try:
                keybd = ctypes.windll.user32.keybd_event
                keybd(18, 0, 0, 0)
                thread1 = win32gui.GetWindowThreadProcessId(hwnd)[0]
                thread2 = win32gui.GetWindowThreadProcessId(foreground)[0]
                ctypes.windll.user32.AttachThreadInput(thread2, thread1, True)
                win32gui.BringWindowToTop(foreground)
                win32gui.SetForegroundWindow(foreground)
                ctypes.windll.user32.AttachThreadInput(thread2, thread1, False)
                keybd(18, 0, 2, 0)
            except Exception:
                pass
        return True
    except Exception:
        return False

def clip_cursor(rect=None):
    try:
        if rect is None:
            ctypes.windll.user32.ClipCursor(None)
        else:
            value = wintypes.RECT(*rect)
            ctypes.windll.user32.ClipCursor(ctypes.byref(value))
    except Exception:
        pass
_MOUSE_LOCKERS = set()

def unlock_all_mouse():
    for runner in list(_MOUSE_LOCKERS):
        try:
            runner._mouse_locked = False
            runner._user_unlock = True
        except Exception:
            pass
    _MOUSE_LOCKERS.clear()
    clip_cursor()

def restore_offscreen_window(hwnd=None):
    try:
        hwnd = hwnd or load_settings().get('bind_hwnd', 0)
        if not hwnd or not win32gui.IsWindow(hwnd):
            return False
        rect = win32gui.GetWindowRect(hwnd)
        if rect[0] < -10000:
            width, height = (rect[2] - rect[0], rect[3] - rect[1])
            screen_width = win32api.GetSystemMetrics(0)
            screen_height = win32api.GetSystemMetrics(1)
            ctypes.windll.user32.SetWindowPos(hwnd, 0, max(0, (screen_width - width) // 2), max(0, (screen_height - height) // 2), width, height, 20)
            return True
    except Exception:
        pass
    return False

def capture_window_bgr(hwnd):
    hwnd_dc = source_dc = save_dc = bitmap = old_bitmap = None
    image = None
    rect = (0, 0, 0, 0)
    try:
        try:
            if win32gui.IsIconic(hwnd):
                _restore_offscreen(hwnd)
                time.sleep(0.2)
        except Exception:
            pass
        rect = win32gui.GetWindowRect(hwnd)
        width, height = (rect[2] - rect[0], rect[3] - rect[1])
        if width <= 0 or height <= 0:
            return (None, 0, 0)
        hwnd_dc = win32gui.GetWindowDC(hwnd)
        source_dc = win32ui.CreateDCFromHandle(hwnd_dc)
        save_dc = source_dc.CreateCompatibleDC()
        bitmap = win32ui.CreateBitmap()
        bitmap.CreateCompatibleBitmap(source_dc, width, height)
        old_bitmap = save_dc.SelectObject(bitmap)
        ctypes.windll.user32.PrintWindow(hwnd, save_dc.GetSafeHdc(), 2)
        info = bitmap.GetInfo()
        bits = bitmap.GetBitmapBits(True)
        image = np.frombuffer(bits, dtype=np.uint8).reshape((info['bmHeight'], info['bmWidth'], 4))[:, :, :3].copy()
    except Exception:
        image = None
    finally:
        try:
            if old_bitmap is not None:
                save_dc.SelectObject(old_bitmap)
            if bitmap is not None:
                win32gui.DeleteObject(bitmap.GetHandle())
            if save_dc is not None:
                save_dc.DeleteDC()
            if source_dc is not None:
                source_dc.DeleteDC()
            if hwnd_dc is not None:
                win32gui.ReleaseDC(hwnd, hwnd_dc)
        except Exception:
            pass
    if image is None or image.size == 0:
        return (None, 0, 0)
    return (image, rect[0], rect[1])

def ensure_foreground(hwnd):
    try:
        rect = win32gui.GetWindowRect(hwnd)
        moved = False
        if rect[0] < -10000 or rect[1] < -10000:
            width, height = (rect[2] - rect[0], rect[3] - rect[1])
            sw = ctypes.windll.user32.GetSystemMetrics(0)
            sh = ctypes.windll.user32.GetSystemMetrics(1)
            ctypes.windll.user32.SetWindowPos(hwnd, 0, max(0, (sw - width) // 2), max(0, (sh - height) // 2), width, height, 20)
            moved = True
        if win32gui.GetForegroundWindow() == hwnd:
            return True
        if win32gui.IsIconic(hwnd):
            win32gui.ShowWindow(hwnd, win32con.SW_RESTORE)
        if moved:
            time.sleep(0.3)
        keybd = ctypes.windll.user32.keybd_event
        target_thread = win32gui.GetWindowThreadProcessId(hwnd)[0]
        for _ in range(3):
            if win32gui.GetForegroundWindow() == hwnd:
                break
            foreground = win32gui.GetForegroundWindow()
            foreground_thread = win32gui.GetWindowThreadProcessId(foreground)[0] if foreground else 0
            try:
                keybd(18, 0, 0, 0)
            except Exception:
                pass
            try:
                ctypes.windll.user32.AttachThreadInput(foreground_thread, target_thread, True)
                win32gui.BringWindowToTop(hwnd)
                win32gui.SetForegroundWindow(hwnd)
                ctypes.windll.user32.AttachThreadInput(foreground_thread, target_thread, False)
            except Exception:
                try:
                    win32gui.SetForegroundWindow(hwnd)
                except Exception:
                    pass
            try:
                keybd(18, 0, 2, 0)
            except Exception:
                pass
            try:
                win32gui.SetActiveWindow(hwnd)
            except Exception:
                pass
            for _ in range(3):
                if win32gui.GetForegroundWindow() == hwnd:
                    return True
                time.sleep(0.15)
        return win32gui.GetForegroundWindow() == hwnd
    except Exception:
        return False

def pct_to_abs(pct, total):
    return int(total * pct / 100)

def cfg_region(cfg, rect):
    x, y, x2, y2 = rect
    width, height = (x2 - x, y2 - y)
    region_x = x + pct_to_abs(cfg.get('x_pct', 0), width)
    region_y = y + pct_to_abs(cfg.get('y_pct', 0), height)
    region_width = max(1, pct_to_abs(cfg.get('w_pct', 1), width))
    region_height = max(1, pct_to_abs(cfg.get('h_pct', 1), height))
    return (region_x, region_y, region_width, region_height)

def find_window_by_title(title):
    if not title:
        return 0
    result = []

    def callback(hwnd, _):
        if win32gui.IsWindowVisible(hwnd):
            try:
                if win32gui.GetWindowText(hwnd) == title:
                    result.append(hwnd)
            except Exception:
                pass
        return True
    try:
        win32gui.EnumWindows(callback, None)
    except Exception:
        return 0
    if not result:
        return 0
    if len(result) == 1:
        return result[0]
    best, best_area = (0, 0)
    for hwnd in result:
        try:
            rect = win32gui.GetWindowRect(hwnd)
            area = (rect[2] - rect[0]) * (rect[3] - rect[1])
            if area > best_area:
                best, best_area = (hwnd, area)
        except Exception:
            pass
    return best

class Screen:
    _grab_lock = threading.Lock()
    _dxcam_ok_until = 0.0

    def __init__(self, title=''):
        self.hwnd = None
        self._rc = None
        self._rct = 0
        self._dxcam = None
        self._dx_gen = -1
        if title:
            result = []

            def callback(hwnd, _):
                if title.lower() in win32gui.GetWindowText(hwnd).lower():
                    result.append(hwnd)
                    return False
                return True
            win32gui.EnumWindows(callback, None)
            if result:
                self.hwnd = result[0]
                return
        self.hwnd = win32gui.GetForegroundWindow()

    def rect(self):
        now = time.time()
        if self._rc and now - self._rct < 0.1:
            return self._rc
        if self.hwnd:
            try:
                rect = win32gui.GetWindowRect(self.hwnd)
                if rect[2] - rect[0] > 100 and rect[3] - rect[1] > 100:
                    self._rc, self._rct = (rect, now)
                    return rect
            except Exception as exc:
                print(f'[DD.WindowRect] {exc}')
        width = height = 0
        try:
            if self._dxcam is not None:
                width = int(self._dxcam.width or 0)
                height = int(self._dxcam.height or 0)
        except Exception:
            pass
        if width < 1 or height < 1:
            width = win32api.GetSystemMetrics(win32con.SM_CXSCREEN)
            height = win32api.GetSystemMetrics(win32con.SM_CYSCREEN)
        self._rc, self._rct = ((0, 0, width, height), now)
        return self._rc

    def grab(self, bbox):
        x, y, x2, y2 = bbox
        width, height = (x2 - x, y2 - y)
        if width < 1 or height < 1:
            return None
        if time.time() >= Screen._dxcam_ok_until:
            with Screen._grab_lock:
                try:
                    camera = self._dxcam
                    if camera is None or self._dx_gen != dxcam_epoch():
                        camera = new_dxcam()
                        self._dxcam = camera
                        self._dx_gen = dxcam_epoch()
                    if camera is not None:
                        frame = camera.grab(region=(x, y, x2, y2))
                        if frame is not None:
                            self._dx_none = 0
                            if frame.ndim == 2:
                                return np.stack([frame, frame, frame], axis=-1).copy()
                            return frame[:, :, :3].copy()
                        self._dx_none = getattr(self, '_dx_none', 0) + 1
                        if self._dx_none >= 500:
                            self._dx_none = 0
                            self._dxcam = None
                            reset_dxcam()
                            Screen._dxcam_ok_until = time.time() + 60.0
                        return None
                except Exception as exc:
                    self._dxcam = None
                    reset_dxcam()
                    Screen._dxcam_ok_until = time.time() + 1.0
                    _log_cam_error(f'[DD.dxcam_grab] {exc}')
        hwnd = self.hwnd or win32gui.GetDesktopWindow()
        hdc = memory_dc = source_dc = bitmap = old_bitmap = None
        try:
            hdc = win32gui.GetWindowDC(hwnd)
            source_dc = win32ui.CreateDCFromHandle(hdc)
            memory_dc = source_dc.CreateCompatibleDC()
            bitmap = win32ui.CreateBitmap()
            bitmap.CreateCompatibleBitmap(source_dc, width, height)
            old_bitmap = memory_dc.SelectObject(bitmap)
            source_x, source_y = (x, y)
            if self.hwnd:
                rect = win32gui.GetWindowRect(self.hwnd)
                source_x, source_y = (x - rect[0], y - rect[1])
            memory_dc.BitBlt((0, 0), (width, height), source_dc, (source_x, source_y), win32con.SRCCOPY)
            bits = bitmap.GetBitmapBits(True)
            image = np.frombuffer(bits, dtype=np.uint8).reshape((height, width, 4))
            if image.size and float(np.max(image)) < 8.0:
                return None
            return image[:, :, :3].copy()
        except Exception:
            return None
        finally:
            try:
                if old_bitmap is not None:
                    memory_dc.SelectObject(old_bitmap)
                if memory_dc is not None:
                    memory_dc.DeleteDC()
                if source_dc is not None:
                    source_dc.DeleteDC()
                if bitmap is not None:
                    win32gui.DeleteObject(bitmap.GetHandle())
                if hdc is not None:
                    win32gui.ReleaseDC(hwnd, hdc)
            except Exception as exc:
                print(f'[DD.gdi_cleanup] {exc}')

    def release(self):
        try:
            if self._dxcam and self._dx_gen == dxcam_epoch():
                release_dxcam(self._dxcam)
            self._dxcam = None
        except Exception as exc:
            print(f'[Screen.release] {exc}')

    def _color_match(self, img, target_rgb, tol):
        if img.size == 0:
            return False
        target = np.array(target_rgb[::-1], dtype=np.uint8)
        lower = np.clip(target.astype(int) - tol, 0, 255).astype(np.uint8)
        upper = np.clip(target.astype(int) + tol, 0, 255).astype(np.uint8)
        return cv2.countNonZero(cv2.inRange(img, lower, upper)) >= 3

    def check(self, cfg):
        x, y, width, height = cfg_region(cfg, self.rect())
        raw = cfg.get('color')
        if raw is None:
            return False
        target = np.array(raw, dtype=np.int16)
        tolerance = cfg.get('tolerance', cfg.get('tol', DEFAULT_TOLERANCE))
        image = self.grab((x, y, x + width, y + height))
        return False if image is None else self._color_match(image, target, tolerance)

    def ocr(self, bbox, mode='auto'):
        image = self.grab(bbox)
        return '' if image is None else ocr_image(image, mode)

def make_color_rule(x_pct, y_pct, color, **kwargs):
    rule = {'x_pct': x_pct, 'y_pct': y_pct, 'w_pct': 1, 'h_pct': 1, 'color': list(color), 'tol': DEFAULT_TOL}
    rule.update(kwargs)
    tolerance = rule.get('tolerance', rule.get('tol', DEFAULT_TOL))
    rule['tol'] = tolerance
    rule['tolerance'] = tolerance
    return rule

def ocr_image_bingtop(img_bgr):
    global _BINGTOP_CREDS, _BINGTOP_LAST_LOAD
    now = time.time()
    if _BINGTOP_CREDS is None or now - _BINGTOP_LAST_LOAD > 60:
        settings = load_settings()
        url = settings.get('bingtop_url') or 'https://www.bingtop.com/ocr/upload/'
        if url.startswith('http://'):
            url = 'https://' + url[7:]
        _BINGTOP_CREDS = {'url': url, 'username': settings.get('bingtop_user', ''), 'password': settings.get('bingtop_pwd', ''), 'captcha_type': int(settings.get('bingtop_type', '1017')), 'timeout': int(settings.get('bingtop_timeout', '60'))}
        _BINGTOP_LAST_LOAD = now
    if not _BINGTOP_CREDS['username'] or not _BINGTOP_CREDS['password']:
        return ''
    try:
        import requests
        _, encoded_image = cv2.imencode('.png', img_bgr)
        encoded = base64.b64encode(encoded_image).decode('ascii')
        params = {'username': _BINGTOP_CREDS['username'], 'password': _BINGTOP_CREDS['password'], 'captchaData': encoded, 'captchaType': _BINGTOP_CREDS['captcha_type']}
        response = requests.post(_BINGTOP_CREDS['url'], data=params, timeout=_BINGTOP_CREDS['timeout'])
        payload = response.json()
        if payload.get('code') == 0:
            return payload['data'].get('recognition', '')
    except Exception:
        pass
    return ''

def _ocr_preprocess(img_bgr, mode):
    gray = cv2.cvtColor(img_bgr, cv2.COLOR_BGR2GRAY)
    gray = cv2.createCLAHE(clipLimit=2.0, tileGridSize=(8, 8)).apply(gray)
    binary = mode not in ('auto', '', '中文', 'chi')
    if binary:
        gray = cv2.medianBlur(gray, 3)
        _, gray = cv2.threshold(gray, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
    return (gray, binary)
TRA_ONLY_CHARS = frozenset('體藥復擊鳥馬魚車東開關時間點雲學萬發讀釋證護講談聽願從衝殺應對務衛員風陽陰聲響勝愛見這還進過話讓誰認識說錢銀飯館醫院畫門氣龍鳳靈屬敵敗傷業號單問歡興認真準備結離練習驗視覺曉瞭計畫製設計創製造發明鬥豐樂實藝雙麗複雜雖難轉輪較軟體狀態與戰勝敗變傷壞損氣')
_OCR_KEEP = re.compile('[^一-鿿㐀-䶿\u3040-ヿa-zA-Z0-9%.,:/\\-（）()【】\\[\\]：]')

def _clean_ocr_text(text):
    return _OCR_KEEP.sub('', re.sub('\\s+', '', text))

def _ocr_run(gray, is_binary, lang, extra):
    import pytesseract
    versions = [gray] + ([cv2.bitwise_not(gray)] if is_binary else [])
    best = ''
    for version in versions:
        image = Image.fromarray(version)
        width, height = image.size
        scale = max(1, 300 // max(width, 32))
        if scale > 1:
            image = image.resize((width * scale, height * scale), Image.LANCZOS)
        for psm in OCR_PSM_ORDER:
            try:
                text = pytesseract.image_to_string(image, lang=lang, config=f'--oem 1 --psm {psm} {extra}'.strip())
                text = _clean_ocr_text(text)
                if len(text) > len(best):
                    best = text
            except Exception as exc:
                print(f'[DD.ocr_psm] {exc}')
    return best

def _is_traditional(text):
    return any((char in TRA_ONLY_CHARS for char in text))

def ocr_image(img_bgr, mode='auto'):
    if mode in ('冰拓', 'bingtop'):
        return ocr_image_bingtop(img_bgr)
    try:
        import pytesseract
        tesseract = get_tesseract_path()
        if tesseract:
            pytesseract.pytesseract.tesseract_cmd = tesseract
        if mode in OCR_MODES:
            lang, extra = OCR_MODES[mode]
        elif mode and mode != 'auto':
            lang, extra = ('eng', f'-c tessedit_char_whitelist={mode}')
        else:
            lang, extra = ('chi_sim+eng', '')
        gray, binary = _ocr_preprocess(img_bgr, mode)
        if mode in ('中文', 'chi'):
            simplified = _ocr_run(gray, binary, 'chi_sim', '')
            traditional = _ocr_run(gray, binary, 'chi_tra', '')
            if traditional and _is_traditional(traditional):
                return traditional if len(traditional) <= 50 else simplified if simplified and len(simplified) <= 50 else ''
            best = simplified or traditional
            return best if best and len(best) <= 50 else ''
        best = _ocr_run(gray, binary, lang, extra)
        return best if best and len(best) <= 50 else ''
    except Exception as exc:
        print(f'[DD.ocr] {exc}')
        return ''
_tts_lock = threading.Lock()
_tts_last = {'text': None, 't': 0.0}
_TTS_PROC_LOCK = threading.Lock()
_TTS_PROC = None
_TTS_PLAY_LOCK = threading.Lock()
_TTS_PLAY_PROC = None

def _ensure_tts_proc():
    global _TTS_PROC
    with _TTS_PROC_LOCK:
        if _TTS_PROC is not None and _TTS_PROC.poll() is None:
            return True
        try:
            import subprocess
            script = "[Console]::InputEncoding=[Text.Encoding]::UTF8;Add-Type -AssemblyName System.Speech;$s=New-Object System.Speech.Synthesis.SpeechSynthesizer;$s.Volume=100;foreach($v in $s.GetInstalledVoices()){if($v.VoiceInfo.Culture.ToString() -like 'zh*'){$s.SelectVoice($v.VoiceInfo.Name);break}};while($true){try{$line=Read-Host}catch{break};if($null -eq $line -or '' -eq $line){break};$i=$line.IndexOf([char]9);if($i -lt 0){continue};$s.SetOutputToWaveFile($line.Substring($i+1));try{$s.Speak($line.Substring(0,$i))}catch{};$s.SetOutputToDefaultAudioDevice()}"
            _TTS_PROC = subprocess.Popen(['powershell', '-NoProfile', '-Command', script], stdin=subprocess.PIPE, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, creationflags=getattr(subprocess, 'CREATE_NO_WINDOW', 0))
            return _TTS_PROC.poll() is None
        except Exception:
            _TTS_PROC = None
            return False

def _ensure_play_proc():
    global _TTS_PLAY_PROC
    with _TTS_PLAY_LOCK:
        if _TTS_PLAY_PROC is not None and _TTS_PLAY_PROC.poll() is None:
            return True
        try:
            import subprocess
            script = "Add-Type -AssemblyName PresentationFramework;$p=[System.Windows.Media.MediaPlayer]::new();$p.Volume=1.0;while($true){try{$f=Read-Host}catch{break};if($null -eq $f -or '' -eq $f){break};try{$p.Close();$p.Open($f);$p.Play();$t0=[DateTime]::Now;while(-not $p.NaturalDuration.HasTimeSpan -and ([DateTime]::Now-$t0).TotalSeconds -lt 2){Start-Sleep -Milliseconds 50};$dur=60.0;try{if($p.NaturalDuration.HasTimeSpan){$dur=$p.NaturalDuration.TimeSpan.TotalSeconds}}catch{};if($dur -gt 60 -or $dur -le 0){$dur=60};$t1=[DateTime]::Now;while(([DateTime]::Now-$t1).TotalSeconds -lt $dur){Start-Sleep -Milliseconds 100}}catch{}}"
            _TTS_PLAY_PROC = subprocess.Popen(['powershell', '-NoProfile', '-Command', script], stdin=subprocess.PIPE, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, creationflags=getattr(subprocess, 'CREATE_NO_WINDOW', 0))
            return _TTS_PLAY_PROC.poll() is None
        except Exception:
            _TTS_PLAY_PROC = None
            return False

def _synth_edge(text, path):
    for _ in range(2):
        try:
            import edge_tts

            async def synthesize():
                communicator = edge_tts.Communicate(str(text), 'zh-CN-XiaoxiaoNeural')
                await communicator.save(str(path))
            asyncio.run(asyncio.wait_for(synthesize(), timeout=15))
            if os.path.exists(path) and os.path.getsize(path) > 500:
                return True
        except Exception:
            pass
        try:
            os.remove(path)
        except Exception:
            pass
    return False

def tts_speak_func(text):
    try:
        if not load_settings().get('voice', False):
            return
    except Exception:
        pass
    with _tts_lock:
        now = time.time()
        if text == _tts_last['text'] and now - _tts_last['t'] < 3.0:
            return
        _tts_last['text'], _tts_last['t'] = (text, now)

    def speak():
        import tempfile
        cache_dir = os.path.join(tempfile.gettempdir(), 'ke_tts_cache')
        os.makedirs(cache_dir, exist_ok=True)
        try:
            files = [os.path.join(cache_dir, name) for name in os.listdir(cache_dir)]
            if len(files) > 300:
                for filename in sorted(files, key=os.path.getmtime)[:len(files) // 2]:
                    os.remove(filename)
        except Exception:
            pass
        key = hashlib.md5(str(text).encode('utf-8')).hexdigest()[:16]
        mp3 = os.path.join(cache_dir, f'ke_tts_{key}.mp3')
        wav = os.path.join(cache_dir, f'ke_tts_{key}.wav')
        play = mp3 if os.path.exists(mp3) else wav if os.path.exists(wav) else None
        if play is None and _synth_edge(text, mp3):
            play = mp3
        try:
            if play and _ensure_play_proc():
                _TTS_PLAY_PROC.stdin.write((play + '\n').encode('utf-8'))
                _TTS_PLAY_PROC.stdin.flush()
        except Exception:
            pass
    threading.Thread(target=speak, daemon=True).start()

def warm_tts():
    try:
        (_ensure_tts_proc(), _ensure_play_proc())
    except Exception:
        pass
    try:
        import tempfile
        cache_dir = os.path.join(tempfile.gettempdir(), 'ke_tts_cache')
        os.makedirs(cache_dir, exist_ok=True)
        for text in ('KeDriver已开启', 'KeDriver已关闭'):
            key = hashlib.md5(text.encode('utf-8')).hexdigest()[:16]
            path = os.path.join(cache_dir, f'ke_tts_{key}.mp3')
            if not os.path.exists(path):
                _synth_edge(text, path)
    except Exception:
        pass

class LuaRunner:
    _next_gen = 0

    def __init__(self, lua_code, log_cb=None, status_cb=None, input_mode='KEDriver', app=None):
        self.log = log_cb or (lambda _message: None)
        self.status = status_cb or (lambda *_args: None)
        self._app = app
        self._suspend_until = 0.0
        if input_mode == 'SendInput':
            self.dd = KEDriverInput()
            self._kb = SendInputKB()
        elif input_mode == 'DD64':
            self.dd = DDInput()
        elif str(input_mode).lower() == 'fakerinput':
            self.dd = FakerInputInput()
        elif str(input_mode).lower() == 'viiper':
            self.dd = ViiperInput()
        else:
            self.dd = KEDriverInput()
        self._bind_title = ''
        self._rebind_ts = 0.0
        try:
            settings = load_settings()
            hwnd = settings.get('bind_hwnd', 0)
            self._bind_title = settings.get('bind_title', '') or ''
            if hwnd and (not win32gui.IsWindow(hwnd)):
                new_hwnd = find_window_by_title(self._bind_title)
                if new_hwnd:
                    hwnd = new_hwnd
                    settings['bind_hwnd'] = new_hwnd
                    save_settings(settings)
            self.scr = Screen('')
            self.scr.hwnd = hwnd if hwnd and win32gui.IsWindow(hwnd) else None
        except Exception:
            self.scr = Screen('')
            self.scr.hwnd = None
        self._stop_event = threading.Event()
        self._mouse_locked = False
        self._user_unlock = False
        self._lock_thr = None
        self._driver_lock = threading.Lock()
        self._keys_pressed = set()
        self._mem = None
        self._async_thread = None
        self._async_paused = False
        self._async_detect_fn = None
        self._err_count = 0
        self._captcha_lock = threading.Lock()
        self._captcha_busy = False
        self._captcha_pending = False
        self._transform_until = 0.0
        self._captcha_quiet_until = 0.0
        self._cached_win_frame = False
        self._cached_rect = None
        self._pitch_last = [0.0, 0]
        self._thread = None
        self._gen = 0
        self._lua_last_run = time.perf_counter()
        if '_fls' not in lua_code:
            if 'function on_start()' in lua_code:
                lua_code = lua_code.replace('function on_start()', 'local _fls = float_status\n\nfunction on_start()\n    _fls("启动","#10b981")', 1)
            elif 'on_tick' in lua_code:
                lua_code = 'local _fls = float_status\n' + lua_code
        self._code = lua_code
        from lupa import LuaRuntime
        self._lua = LuaRuntime(unpack_returned_tuples=True)
        self._inject_api()
        try:
            self._lua.execute(self._code)
            globals_table = self._lua.globals()
            self._on_start = globals_table['on_start']
            self._on_tick = globals_table['on_tick']
            self._on_stop = globals_table['on_stop']
            if not self._on_tick:
                raise RuntimeError('Lua需要on_tick()')
        except Exception:
            self._stop_event.set()
            raise

    def _ensure_bind(self):
        hwnd = self.scr.hwnd
        if not hwnd or win32gui.IsWindow(hwnd):
            return
        now = time.time()
        if now - self._rebind_ts < 5:
            return
        self._rebind_ts = now
        new_hwnd = find_window_by_title(self._bind_title)
        if new_hwnd and win32gui.IsWindow(new_hwnd):
            self.scr.hwnd = new_hwnd
            self.scr._rc = None
            try:
                settings = load_settings()
                settings['bind_hwnd'] = new_hwnd
                save_settings(settings)
                if self._app and getattr(self._app, 'settings', None):
                    self._app.settings['bind_hwnd'] = new_hwnd
            except Exception:
                pass
            self.log(f'[绑定] 句柄失效, 已按标题重找: {new_hwnd}')

    def _lock_loop(self):
        try:
            while self._mouse_locked:
                try:
                    rect = self.scr.rect()
                    if rect and rect[2] > rect[0]:
                        clip_cursor(rect)
                except Exception:
                    pass
                time.sleep(0.2)
        finally:
            clip_cursor()
            _MOUSE_LOCKERS.discard(self)

    def set_mouse_lock(self, lock):
        self._mouse_locked = bool(lock)
        if lock:
            self._user_unlock = False
            if self._lock_thr is None or not self._lock_thr.is_alive():
                _MOUSE_LOCKERS.add(self)
                self._lock_thr = threading.Thread(target=self._lock_loop, daemon=True)
                self._lock_thr.start()
            self.log('[鼠标] 已锁定窗口中央, 按 Ctrl+Alt+F9 解锁')
            app_ref = getattr(self, '_app_ref', None)
            if app_ref:
                app_ref._float_blink('鼠标已锁定 · Ctrl+Alt+F9 解锁', '#f97316')
        else:
            clip_cursor()

    def suspend_inject(self, seconds=3600):
        self._suspend_until = time.time() + seconds

    def resume_inject(self):
        self._suspend_until = 0.0

    @staticmethod
    def _lua_table_to_dict(table):
        if table is None:
            return {}
        if hasattr(table, 'items'):
            return {str(key): LuaRunner._lua_table_to_dict(value) if hasattr(value, 'items') else value for key, value in table.items()}
        return {}

    def _inject_api(self):
        globals_table = self._lua.globals()
        driver = self.dd
        keyboard = getattr(self, '_kb', driver)
        tracked = self._keys_pressed
        stop_event = self._stop_event
        self._api_refs = []
        frame_cache = {'img': None, 't': 0.0, 'r': None}
        image_list = {'files': [], 't': 0.0}
        image_hold = {}

        def expose(name, function):
            globals_table[name] = function
            self._api_refs.append(function)

        def key_down(key):
            keyboard.kd(key)
            tracked.add(('k', str(key).lower()))

        def key_up(key):
            keyboard.ku(key)
            tracked.discard(('k', str(key).lower()))

        def sleep_ms(ms):
            if ms <= 15:
                end = time.perf_counter() + ms / 1000
                while time.perf_counter() < end:
                    pass
            else:
                stop_event.wait(ms / 1000)

        def key_press(key, ms=1):
            self.log(f'[键]{key}·{ms}ms')
            (key_down(key), sleep_ms(ms), key_up(key))

        def mouse_down(name, marker):
            getattr(driver, name)()
            tracked.add(marker)

        def mouse_up(name, marker):
            getattr(driver, name)()
            tracked.discard(marker)

        def mouse_move_rel(dx, dy):
            driver.move_r(int(dx), int(dy))

        def mouse_move_to(x, y):
            driver.move_to(int(x), int(y))

        def mouse_move_win(x_percent, y_percent):
            rect = self.scr.rect()
            driver.move_to(int(rect[0] + (rect[2] - rect[0]) * x_percent / 100), int(rect[1] + (rect[3] - rect[1]) * y_percent / 100))

        def get_frame():
            nonlocal frame_cache
            now = time.time()
            if frame_cache['img'] is not None and now - frame_cache['t'] < FRAME_CACHE_INTERVAL:
                return (frame_cache['img'], frame_cache['r'])
            self._ensure_bind()
            rect = self.scr.rect()
            full = self.scr.grab(rect)
            if full is None:
                return (frame_cache['img'], frame_cache['r']) if frame_cache['img'] is not None else (None, rect)
            if full.ndim == 2:
                full = np.stack([full, full, full], axis=-1)
            frame_cache = {'img': full, 't': now, 'r': rect}
            return (full, rect)

        def as_dict(value):
            return self._lua_table_to_dict(value) if hasattr(value, 'items') else dict(value or {})

        def check_color(name):
            config = self._get_color_config(str(name))
            return self.scr.check(config) if config else False

        def ocr_read(x, y, width, height, mode='auto'):
            rect = self.scr.rect()
            window_width, window_height = (rect[2] - rect[0], rect[3] - rect[1])
            return self.scr.ocr((rect[0] + int(window_width * x / 100), rect[1] + int(window_height * y / 100), rect[0] + int(window_width * (x + width) / 100), rect[1] + int(window_height * (y + height) / 100)), mode)

        def clipboard_write(value):
            from captcha_service import set_clipboard as write
            return write(str(value))

        def paste_text():
            (keyboard.kd('ctrl'), tracked.add(('k', 'ctrl')))
            (keyboard.kd('v'), tracked.add(('k', 'v')))
            time.sleep(0.02)
            (keyboard.ku('v'), tracked.discard(('k', 'v')))
            (keyboard.ku('ctrl'), tracked.discard(('k', 'ctrl')))

        def type_text(value):
            (clipboard_write(str(value)), time.sleep(0.05), paste_text())

        def write_cmd(key, value):
            settings = load_settings()
            settings[str(key)] = value
            return save_settings(settings)
        globals_table['_saved_color_rules'] = {}

        def save_color_rule(name, config_list):
            globals_table._saved_color_rules[name] = list(config_list)
            if self._app and getattr(self._app, '_current_script', None):
                rules = self._app.settings.setdefault('color_rules', {})
                rules[self._app._current_script] = dict(globals_table._saved_color_rules)
                save_settings(self._app.settings)

        def color_rules_now():
            if not self._app or not getattr(self._app, '_current_script', None):
                return dict(globals_table._saved_color_rules)
            script = self._app._current_script
            rules = self._app.settings.get('color_rules', {}).get(script, {})
            enabled = self._app.settings.get('color_rules_enabled', {}).get(script, {})
            return {name: list(config) for name, config in rules.items() if enabled.get(name, True)}

        def check_saved_colors(name):
            configs = color_rules_now().get(str(name), [])
            return any((self.scr.check(as_dict(config)) for config in configs))
        globals_table['_mem_rules'] = {}

        def load_mem_rules():
            rules = {}
            deleted = {}
            if self._app and getattr(self._app, '_current_script', None):
                deleted = self._app.settings.get('rules_deleted', {}).get(self._app._current_script, {}) or {}
            for line in self._code.split('\n'):
                stripped = line.strip()
                if not stripped.startswith('-- @mem '):
                    continue
                parts = stripped[8:].strip().split(None, 3)
                if len(parts) < 2 or parts[0] in deleted:
                    continue
                name = parts[0]
                address_parts = parts[1].split(',')
                base = address_parts[0].strip()
                offsets = [int(item.strip(), 16) if item.strip().startswith('0x') else int(item.strip()) for item in address_parts[1:]]
                dtype = parts[2].strip() if len(parts) > 2 else 'i32'
                expect = {}
                if len(parts) > 3:
                    text = parts[3].strip()
                    if text in ('!=0', 'nonzero'):
                        expect = {'nonzero': True}
                    else:
                        for operation in ('>=', '<=', '!=', '==', '>', '<'):
                            if text.startswith(operation):
                                expect = {'op': operation, 'value': int(text[len(operation):])}
                                break
                rules[name] = {'base': base, 'offsets': offsets, 'type': dtype, 'expect': expect}
            if self._app and getattr(self._app, '_current_script', None):
                stored = self._app.settings.setdefault('memory_rules', {}).setdefault(self._app._current_script, {})
                changed = False
                for name, rule in rules.items():
                    if name not in stored:
                        stored[name] = dict(rule)
                        stored[name].setdefault('enabled', False)
                        changed = True
                    rules[name]['enabled'] = bool(stored[name].get('enabled', True))
                for name, rule in stored.items():
                    if name not in rules:
                        rules[name] = dict(rule)
                if changed:
                    save_settings(self._app.settings)
            globals_table['_mem_rules'] = rules

        def get_memory():
            if self._mem and self._mem.attached:
                return self._mem
            with _MEM_INIT_LOCK:
                if self._mem and self._mem.attached:
                    return self._mem
                settings = load_settings()
                memory = self._mem or KeMem(log_cb=self.log)
                hwnd = settings.get('bind_hwnd', 0)
                title = settings.get('bind_title', '')
                attached = memory.attach_by_hwnd(hwnd) if hwnd else memory.attach_by_title(title) if title else False
                self._mem = memory
                with _mem_viz_lock:
                    _mem_viz.update({'connected': bool(attached), 'pid': memory.pid, 'bits': memory.bits or 0, 'err': '' if attached else memory.last_error_text, 'attach': str(hwnd or title)})
                return memory if attached else None
        self._get_mem = get_memory

        def current_rule(name):
            if self._app and getattr(self._app, '_current_script', None):
                return self._app.settings.get('memory_rules', {}).get(self._app._current_script, {}).get(name)
            return as_dict(globals_table._mem_rules).get(name)

        def mem_check(name):
            rule = current_rule(str(name))
            if rule is None or not rule.get('enabled', True):
                return None
            memory = get_memory()
            if memory is None:
                return None
            value = memory.chain_read(rule.get('base'), rule.get('offsets', []), rule.get('type', 'i32'))
            if value is None:
                return None
            hit = eval_expect(value, rule.get('expect'))
            with _mem_viz_lock:
                _mem_viz['rules'][str(name)] = {'addr': str(rule.get('base')) + ' ' + ' '.join((f'[{offset:#x}]' for offset in rule.get('offsets', []))), 'value': value, 'expect': rule.get('expect'), 'hit': hit, 'ts': time.time()}
            return hit

        def mem_read(name, offsets_table=None):
            rule = as_dict(globals_table._mem_rules).get(str(name))
            memory = get_memory()
            if rule is None or memory is None:
                return None
            offsets = list(offsets_table.values()) if offsets_table else rule.get('offsets', [])
            return memory.chain_read(rule.get('base'), offsets, rule.get('type', 'i32'))

        def mem_read_raw(base, offsets_table=None, dtype_str='i32'):
            memory = get_memory()
            if memory is None:
                return None
            offsets = list(offsets_table.values()) if offsets_table else []
            return memory.chain_read(base, offsets, str(dtype_str))

        def mem_status():
            memory = get_memory()
            return {'ok': bool(memory), 'pid': memory.pid if memory else 0, 'bits': memory.bits if memory and memory.bits else 0, 'error': '' if memory else self._mem.last_error_text if self._mem else '未初始化'}

        def mem_save_rule(name, rule_table):
            rule = as_dict(rule_table)
            globals_table._mem_rules[str(name)] = rule
            if self._app and getattr(self._app, '_current_script', None):
                stored = self._app.settings.setdefault('memory_rules', {}).setdefault(self._app._current_script, {})
                stored[str(name)] = rule
                save_settings(self._app.settings)
            return True

        def mem_aob(pattern, start_addr, scan_size):
            memory = get_memory()
            if memory is None:
                return None
            results = memory.aob_scan(str(pattern), str(start_addr), int(scan_size), max_results=1)
            return results[0] if results else None

        def color_distance(image, blue, green, red):
            difference = image.astype(np.float32) - np.array([blue, green, red], dtype=np.float32)
            return np.clip(np.abs(difference).max(axis=1 if image.ndim == 2 else 2) / 255.0, 0, 1)

        def find_color(config):
            config = as_dict(config)
            full, rect = get_frame()
            if full is None:
                return None
            x, y, width, height = cfg_region(config, rect)
            raw = config.get('color')
            if raw is None:
                return None
            x0, y0 = (max(0, x - rect[0]), max(0, y - rect[1]))
            x1, y1 = (min(full.shape[1], x0 + width), min(full.shape[0], y0 + height))
            image = full[y0:y1, x0:x1]
            if image.size == 0:
                return None
            target = np.array(raw, dtype=np.uint8)[::-1]
            tolerance = config.get('tolerance', config.get('tol', DEFAULT_TOL))
            mask = color_distance(image, *map(int, target)) <= tolerance / 255.0
            count = int(np.count_nonzero(mask))
            if count < 3:
                return None
            ys, xs = np.where(mask)
            globals_table['_last_confidence'] = round(count / mask.size, 3)
            return (round((x + int(xs.mean()) - rect[0]) / (rect[2] - rect[0]) * 100, 2), round((y + int(ys.mean()) - rect[1]) / (rect[3] - rect[1]) * 100, 2))

        def count_color(config):
            config = as_dict(config)
            full, rect = get_frame()
            if full is None:
                return 0
            x, y, width, height = cfg_region(config, rect)
            raw = config.get('color')
            if raw is None:
                return 0
            image = full[max(0, y - rect[1]):min(full.shape[0], y - rect[1] + height), max(0, x - rect[0]):min(full.shape[1], x - rect[0] + width)]
            if image.size == 0:
                return 0
            target = np.array(raw, dtype=np.uint8)
            tolerance = config.get('tolerance', config.get('tol', DEFAULT_TOL))
            lower = np.clip(target.astype(int) - tolerance, 0, 255).astype(np.uint8)[::-1]
            upper = np.clip(target.astype(int) + tolerance, 0, 255).astype(np.uint8)[::-1]
            return int(cv2.countNonZero(cv2.inRange(image, lower, upper)))

        def test_color(config):
            config = as_dict(config)
            full, rect = get_frame()
            if full is None:
                return (0, 0)
            x, y, width, height = cfg_region(config, rect)
            raw = config.get('color')
            if raw is None:
                return (0, 0)
            image = full[max(0, y - rect[1]):min(full.shape[0], y - rect[1] + height), max(0, x - rect[0]):min(full.shape[1], x - rect[0] + width)]
            if image.size == 0:
                return (0, 0)
            target = np.array(raw, dtype=np.uint8)
            tolerance = config.get('tolerance', config.get('tol', DEFAULT_TOL))
            mask = cv2.inRange(image, np.clip(target.astype(int) - tolerance, 0, 255).astype(np.uint8)[::-1], np.clip(target.astype(int) + tolerance, 0, 255).astype(np.uint8)[::-1])
            return (int(cv2.countNonZero(mask)), mask.size)

        def pixel_rgb(x_percent, y_percent):
            full, rect = get_frame()
            if full is None:
                return (0, 0, 0)
            px = int((rect[2] - rect[0]) * x_percent / 100)
            py = int((rect[3] - rect[1]) * y_percent / 100)
            if 0 <= py < full.shape[0] and 0 <= px < full.shape[1]:
                bgr = full[py, px]
                return (int(bgr[2]), int(bgr[1]), int(bgr[0]))
            return (0, 0, 0)

        def click_at(xp, yp, button='left', ms=50):
            rect = self.scr.rect()
            ax = int(rect[0] + (rect[2] - rect[0]) * xp / 100)
            ay = int(rect[1] + (rect[3] - rect[1]) * yp / 100)
            driver.move_to(ax, ay)
            time.sleep(CLICK_PRE_DELAY)
            self.log(f'[点]{button}@{xp},{yp}→{ax},{ay}')
            pairs = {'left': ('ml_d', 'ml_u'), 'right': ('mr_d', 'mr_u'), 'middle': ('mm_d', 'mm_u')}
            if button in pairs:
                getattr(driver, pairs[button][0])()
                time.sleep(ms / 1000)
                getattr(driver, pairs[button][1])()

        def find_img(name, threshold=0.8, hold_frames=3):
            files_dir = os.path.join(SCRIPT_DIR, '图库')
            path = os.path.join(files_dir, str(name))
            if not os.path.splitext(path)[1]:
                for extension in ('.png', '.jpg', '.bmp'):
                    if os.path.exists(path + extension):
                        path += extension
                        break
            template = cv2.imdecode(np.fromfile(path, dtype=np.uint8), cv2.IMREAD_UNCHANGED) if os.path.exists(path) else None
            full, rect = get_frame()
            if template is None or full is None:
                return None
            mask = template[:, :, 3] if template.ndim == 3 and template.shape[2] == 4 else None
            template = template[:, :, :3] if template.ndim == 3 else template
            result = cv2.matchTemplate(full, template, cv2.TM_CCOEFF_NORMED, mask=mask)
            _, score, _, location = cv2.minMaxLoc(result)
            globals_table['_last_confidence'] = round(float(score), 3)
            if score < threshold:
                return None
            x = location[0] + template.shape[1] // 2
            y = location[1] + template.shape[0] // 2
            return (round(x / (rect[2] - rect[0]) * 100, 2), round(y / (rect[3] - rect[1]) * 100, 2))
        quick = QuickRecognition(self.scr, driver)

        def captcha_solve(config=None):
            if self._captcha_busy:
                return False
            with self._captcha_lock:
                if self._captcha_busy:
                    return False
                self._captcha_busy = True
            try:
                settings = self._app.settings if self._app and getattr(self._app, 'settings', None) else load_settings()
                solver = CaptchaSolver(driver, settings, self.log, getattr(self._app, '_float_blink', None), transform_cb=self._on_transform)
                self._solver = solver
                solver.set_cached_rect(self._cached_rect)
                solver.solve(as_dict(config))
                return True
            finally:
                self._captcha_busy = False

        def captcha_busy():
            return bool(self._captcha_busy or getattr(getattr(self, '_solver', None), 'busy', False))

        def burst_keys(keys_str, gap_ms=1, hold_ms=1):
            for key in [item.strip() for item in str(keys_str).split(',') if item.strip()]:
                key_down(key)
                if hold_ms > 0:
                    time.sleep(hold_ms / 1000.0)
                key_up(key)
                if gap_ms > 0:
                    time.sleep(gap_ms / 1000.0)

        def float_status(text, color='#10b981'):
            if self._app and hasattr(self._app, '_float_blink'):
                self._app._float_blink(str(text), str(color))
            try:
                self.status(str(text), str(color))
            except TypeError:
                self.status(str(text))
        expose('should_stop', stop_event.is_set)
        expose('key_down', key_down)
        expose('key_up', key_up)
        expose('key_press', key_press)
        expose('mouse_left_down', lambda: mouse_down('ml_d', 'ml'))
        expose('mouse_left_up', lambda: mouse_up('ml_u', 'ml'))
        expose('mouse_right_down', lambda: mouse_down('mr_d', 'mr'))
        expose('mouse_right_up', lambda: mouse_up('mr_u', 'mr'))
        expose('mouse_middle', lambda ms=50: (mouse_down('mm_d', 'mm'), sleep_ms(ms), mouse_up('mm_u', 'mm')))
        expose('mouse_move_rel', mouse_move_rel)
        expose('mouse_move_to', mouse_move_to)
        expose('mouse_move_win', mouse_move_win)
        expose('mouse_lock', self.set_mouse_lock)
        expose('sleep', sleep_ms)
        expose('now_ms', lambda: int(time.time() * 1000))
        expose('random', lambda a, b: random.randint(int(a), int(b)))
        expose('log', self.log)
        expose('print', self.log)
        expose('tts_speak', tts_speak_func)
        expose('ocr', ocr_read)
        expose('check_color', check_color)
        expose('check', check_color)
        expose('set_clipboard', clipboard_write)
        expose('paste_text', paste_text)
        expose('type_text', type_text)
        expose('write_cmd', write_cmd)
        expose('save_color_rule', save_color_rule)
        expose('check_saved_colors', check_saved_colors)
        expose('mem_check', mem_check)
        expose('mem_read', mem_read)
        expose('mem_read_raw', mem_read_raw)
        expose('mem_status', mem_status)
        expose('mem_save_rule', mem_save_rule)
        expose('mem_aob', mem_aob)
        expose('find_color', find_color)
        expose('count_color', count_color)
        expose('test_color', test_color)
        expose('pixel_rgb', pixel_rgb)
        expose('click_at', click_at)
        expose('find_img', find_img)
        expose('captcha_solve', captcha_solve)
        expose('captcha_busy', captcha_busy)
        expose('burst_keys', burst_keys)
        expose('float_status', float_status)
        expose('quick_color_pick', lambda cfg: quick.runQuickColorPick(as_dict(cfg)))
        expose('quick_color_region', lambda cfg: quick.runQuickColorRegionPick(as_dict(cfg)))
        expose('quick_recognition', lambda cfg: quick.runQuickRecognition(as_dict(cfg)))
        expose('quick_image_capture', lambda cfg: quick.runQuickImageCapture(as_dict(cfg)))
        rect = self.scr.rect()
        globals_table['screen_w'] = rect[2] - rect[0]
        globals_table['screen_h'] = rect[3] - rect[1]
        globals_table['COLORS'] = {}
        load_mem_rules()
        settings = self._app.settings if self._app and getattr(self._app, 'settings', None) else load_settings()
        self._solver = CaptchaSolver(driver, settings, self.log, getattr(self._app, '_float_blink', None), transform_cb=self._on_transform)
        self._async_thread = threading.Thread(target=self._async_loop, daemon=True)
        self._async_thread.start()
        self._ensure_auto_train()

    def _async_loop(self):
        while not self._stop_event.is_set():
            if self._async_detect_fn and (not self._async_paused):
                try:
                    self._async_detect_fn()
                except Exception:
                    pass
            self._stop_event.wait(0.02)

    def set_config(self, json_script):
        globals_table = self._lua.globals()
        colors = json_script.get('color_checks', {})
        globals_table['COLORS'] = {name: {key: value for key, value in config.items() if not key.startswith('_')} for name, config in colors.items()}
        globals_table['CONFIG'] = json_script.get('config', {})

    def _get_color_config(self, name):
        globals_table = self._lua.globals()
        colors = globals_table['COLORS']
        try:
            return self._lua_table_to_dict(colors[name]) if colors and colors[name] else None
        except Exception:
            return None

    def _on_transform(self):
        self._transform_until = time.time() + TRANSFORM_CD_SECONDS
        self._captcha_quiet_until = self._transform_until
        try:
            self.log('[打码] 进入变身冷却20分钟')
        except Exception:
            pass

    def _ensure_auto_train(self):
        thread = getattr(self, '_auto_train_thr', None)
        if thread and thread.is_alive():
            return
        self._auto_train_thr = threading.Thread(target=self._auto_train_loop, daemon=True)
        self._auto_train_thr.start()

    def _auto_train_loop(self):
        while not self._stop_event.wait(600):
            try:
                from captcha_ai_train import glob_all, train_mlp
                positives = glob_all(os.path.join(SHOT_DIR, 'crop'))
                negatives = glob_all(os.path.join(SHOT_DIR, 'normal'))
                if len(positives) >= 10 and len(negatives) >= 10:
                    accuracy = train_mlp(positives, negatives, save_dir=SCRIPT_DIR)
                    _AI_TRAIN_STATE.update({'last_ts': time.time(), 'acc': float(accuracy or 0), 'pos': len(positives), 'neg': len(negatives), 'msg': 'ok'})
            except Exception as exc:
                _AI_TRAIN_STATE['msg'] = str(exc)

    def run(self):
        LuaRunner._next_gen += 1
        self._gen = LuaRunner._next_gen
        self._thread = threading.current_thread()
        self._stop_event.clear()
        try:
            if self._on_start:
                self._on_start()
            while not self._stop_event.is_set():
                if time.time() < self._suspend_until:
                    self._stop_event.wait(0.05)
                    continue
                self._ensure_bind()
                try:
                    self._luacatchup()
                    self._on_tick()
                    self._lua_last_run = time.perf_counter()
                    self._err_count = 0
                except Exception as exc:
                    self.log(f'Lua异常: {exc}')
                    self._err_count += 1
                    if self._err_count >= 10:
                        self.log('[引擎] Lua 连续异常 10 次，自动停止')
                        self._stop_event.set()
                        break
                    self._stop_event.wait(1.5)
                time.sleep(0.015)
        finally:
            try:
                if self._on_stop:
                    self._on_stop()
            except Exception:
                pass
            restore_offscreen_window(load_settings().get('bind_hwnd', 0))
            for item in list(self._keys_pressed):
                try:
                    if isinstance(item, tuple) and item[0] == 'k':
                        self.dd.ku(item[1])
                    elif item == 'ml':
                        self.dd.ml_u()
                    elif item == 'mr':
                        self.dd.mr_u()
                    elif item == 'mm':
                        self.dd.mm_u()
                except Exception:
                    pass
            self._keys_pressed.clear()
            try:
                self.dd.release()
            except Exception:
                pass
            try:
                self.scr.release()
            except Exception:
                pass
            try:
                if self._mem:
                    self._mem.close()
            except Exception:
                pass
            with _mem_viz_lock:
                _mem_viz.update({'connected': False, 'err': '已停止'})
            self.log('>>> 停止 <<<')

    def stop(self):
        self._stop_event.set()
        try:
            solver = getattr(self, '_solver', None)
            if solver:
                solver.cancel()
                started = time.time()
                while solver.busy and time.time() - started < 3:
                    time.sleep(0.05)
        except Exception:
            pass
        try:
            with self._driver_lock:
                self.dd.release()
        except Exception:
            pass
        thread = self._thread
        if thread and thread.is_alive() and (thread is not threading.current_thread()):
            thread.join(timeout=1)

    @staticmethod
    def _imread_or_none(filename):
        try:
            image = cv2.imread(filename, cv2.IMREAD_GRAYSCALE)
            if image is not None:
                return image
        except Exception:
            pass
        try:
            return cv2.imdecode(
                np.fromfile(filename, dtype=np.uint8),
                cv2.IMREAD_GRAYSCALE,
            )
        except Exception:
            return None

    def _smart_gate(self, new_files):
        try:
            from captcha_ai import predict
        except Exception:
            return False
        hits = 0
        for filename in new_files:
            image = self._imread_or_none(filename)
            if image is None:
                continue
            value = predict(image)
            if value is None:
                return False
            if value > 0.5:
                hits += 1
        return hits >= max(1, int(len(new_files) * 0.95))

    @staticmethod
    def _holdout_split(pos_files, new_files):
        hold_count = min(10, max(1, len(new_files) // 5))
        hold_names = {os.path.basename(filename) for filename in new_files[-hold_count:]}
        holdout = [filename for filename in pos_files if os.path.basename(filename) in hold_names]
        train_pos = [filename for filename in pos_files if os.path.basename(filename) not in hold_names]
        return holdout, train_pos

    def _backup_model(self):
        backup = []
        for name in ('captcha_model.xml', 'captcha_model.pkl'):
            path = os.path.join(SCRIPT_DIR, name)
            if os.path.exists(path):
                try:
                    with open(path, 'rb') as stream:
                        backup.append((path, stream.read()))
                except Exception:
                    pass
        return backup

    @staticmethod
    def _restore_model(backup):
        if backup:
            for path, data in backup:
                try:
                    with open(path, 'wb') as stream:
                        stream.write(data)
                except Exception:
                    pass
            return
        for name in ('captcha_model.xml', 'captcha_model.pkl'):
            try:
                os.remove(os.path.join(SCRIPT_DIR, name))
            except Exception:
                pass

    def _luacatchup(self):
        paused = time.perf_counter() - self._lua_last_run
        if paused < 1.0:
            return
        try:
            globals_table = self._lua.globals()
            old_offset = globals_table['_off'] if '_off' in globals_table else 0
            globals_table['_off'] = float(old_offset or 0) + paused * 1000.0
            self._lua_last_run = time.perf_counter()
        except Exception:
            pass

    def _verify_deploy(self, holdout, backup):
        captcha_ai = __import__('captcha_ai', fromlist=('predict', 'reload_model'), level=0)
        predict = captcha_ai.predict
        reload_model = captcha_ai.reload_model
        old_scores = []
        for __temp_4149 in iter(holdout):
            f = __temp_4149
            img = self._imread_or_none(f)
            if img is not None:
                v = predict(img)
                if v is not None:
                    old_scores.append(v)
                    continue
                else:
                    continue
            else:
                continue
        reload_model()
        new_scores = []
        for __temp_4155 in iter(holdout):
            f = __temp_4155
            img = self._imread_or_none(f)
            if img is not None:
                v = predict(img)
                if v is not None:
                    new_scores.append(v)
                    continue
                else:
                    continue
            else:
                continue
        if not new_scores:
            self._restore_model(backup)
            reload_model()
            return False
        if old_scores:
            old_avg = float(np.mean(old_scores))
        else:
            old_avg = 0.5
        new_avg = float(np.mean(new_scores))
        if new_avg >= old_avg - 0.02:
            return True
        self._restore_model(backup)
        reload_model()
        return False

def list_scripts():
    """扫描驱动目录，过滤黑名单"""
    if not os.path.exists(SCRIPTS_DIR):
        os.makedirs(SCRIPTS_DIR)
    s = load_settings()
    removed = s.get('driver_list', [])
    scripts = []
    for f in os.listdir(SCRIPTS_DIR):
        if not f.endswith('.lua') or f in removed:
            continue
        name = f.replace('.lua', '')
        desc = name
        game = ''
        try:
            for line in lua_read_text(os.path.join(SCRIPTS_DIR, f)).splitlines():
                line = line.strip()
                if line.startswith('-- name '):
                    name = line[7:].strip()
                    continue
                if line.startswith('-- game '):
                    game = line[7:].strip()
                    continue
                if '介绍:' in line or '驱动介绍:' in line:
                    desc = line.split(':')[-1].strip()
        except Exception as e:
            print(f'[DD.load_scripts] {e}')
        scripts.append({'file': f, 'name': name, 'desc': desc, 'type': 'lua', 'game': game})
    return scripts

def _km(kind):
    global _KM_DLL
    ctypes = __import__('ctypes', fromlist=None, level=0)
    _ct = ctypes
    if _KM_DLL is None:
        _p = _km_find()
        if not _p:
            raise RuntimeError('缺少 keymod.dll, 请重新安装 KE 外设')
        _KM_DLL = _ct.CDLL(_p)
        _KM_DLL.km_get.argtypes = [_ct.c_char_p, _ct.c_char_p, _ct.POINTER(_ct.c_int)]
        _KM_DLL.km_get.restype = _ct.c_int
    _out = _ct.create_string_buffer(128)
    _n = _ct.c_int(0)
    if _KM_DLL.km_get(kind.encode(), _out, _ct.byref(_n)) != 0:
        raise RuntimeError('keymod.dll 取密钥失败(' + str(kind) + ')')
    return _out.raw[slice(None, _n.value)]

def legacy_hwid():
    global _LEGACY_CACHE
    if _LEGACY_CACHE:
        return _LEGACY_CACHE
    _v = _legacy_read()
    if _v:
        _LEGACY_CACHE = _v
        return _v
    _parts = [os.environ.get('COMPUTERNAME', '')] + _hw_sns()
    _v = hashlib.md5('|'.join(_parts).encode()).hexdigest()[slice(None, 12)]
    _legacy_save(_v)
    _LEGACY_CACHE = _v
    return _v

def invalidate_settings_cache():
    with _SETTINGS_LOCK as __temp_2211:
        _SETTINGS_CACHE['data'] = None
        return None
    return None

_FI_IFACE = '{4d1e55b2-f16f-11cf-88cb-001111000030}'
_FI_DEVCLASS = r'SYSTEM\CurrentControlSet\Control\DeviceClasses\%s' % _FI_IFACE
_FI_CHARS = {}
for _i, _ch in enumerate('abcdefghijklmnopqrstuvwxyz'):
    _FI_CHARS[_ch] = (4 + _i, 0)
for _i, _ch in enumerate('1234567890'):
    _FI_CHARS[_ch] = (30 + _i, 0)
_FI_CHARS.update({
    '-': (45, 0), '=': (46, 0), '[': (47, 0), ']': (48, 0),
    '\\': (49, 0), ';': (51, 0), "'": (52, 0), ',': (54, 0),
    '.': (55, 0), '/': (56, 0), '`': (53, 0),
    '~': (53, 2), '!': (30, 2), '@': (31, 2), '#': (32, 2),
    '$': (33, 2), '%': (34, 2), '^': (35, 2), '&': (36, 2),
    '*': (37, 2), '(': (38, 2), ')': (39, 2), '_': (45, 2),
    '+': (46, 2), '{': (47, 2), '}': (48, 2), '|': (49, 2),
    ':': (51, 2), '"': (52, 2), '<': (54, 2), '>': (55, 2),
    '?': (56, 2),
})
_FI_NAMES = {
    'enter': (40, 0), 'return': (40, 0), 'esc': (41, 0),
    'backspace': (42, 0), 'tab': (43, 0), 'space': (44, 0),
    'capslock': (57, 0), 'insert': (73, 0), 'delete': (76, 0),
    'home': (74, 0), 'end': (77, 0), 'pageup': (75, 0),
    'pagedown': (78, 0), 'left': (80, 0), 'up': (82, 0),
    'right': (79, 0), 'down': (81, 0),
    'lshift': (None, 2), 'rshift': (None, 32), 'shift': (None, 2),
    'lctrl': (None, 1), 'rctrl': (None, 16), 'ctrl': (None, 1),
    'lalt': (None, 4), 'ralt': (None, 64), 'alt': (None, 4),
    'lwin': (None, 8), 'rwin': (None, 128),
}
for _i in range(12):
    _FI_NAMES[f'f{_i + 1}'] = (58 + _i, 0)

class FakerInputInput:

    @staticmethod
    def find_col05():
        import winreg
        try:
            with winreg.OpenKey(
                winreg.HKEY_LOCAL_MACHINE,
                _FI_DEVCLASS,
                access=winreg.KEY_READ | winreg.KEY_WOW64_64KEY,
            ) as hk:
                i = 0
                while True:
                    try:
                        name = winreg.EnumKey(hk, i)
                    except OSError:
                        break
                    i += 1
                    if 'HID#SYSTEM&Col05' not in name:
                        continue
                    path = '\\\\?\\' + name[4:]
                    k32 = ctypes.windll.kernel32
                    k32.CreateFileW.restype = ctypes.wintypes.HANDLE
                    k32.CreateFileW.argtypes = [
                        ctypes.wintypes.LPCWSTR, ctypes.wintypes.DWORD,
                        ctypes.wintypes.DWORD, ctypes.wintypes.LPVOID,
                        ctypes.wintypes.DWORD, ctypes.wintypes.DWORD,
                        ctypes.wintypes.HANDLE,
                    ]
                    k32.WriteFile.argtypes = [
                        ctypes.wintypes.HANDLE, ctypes.wintypes.LPVOID,
                        ctypes.wintypes.DWORD,
                        ctypes.POINTER(ctypes.wintypes.DWORD),
                        ctypes.wintypes.LPVOID,
                    ]
                    k32.WriteFile.restype = ctypes.wintypes.BOOL
                    h = k32.CreateFileW(path, 1073741824, 3, None, 3, 0, None)
                    if h in (None, -1, 0):
                        continue
                    rep = [64, 9, 1, 0, 0, 0, 0, 0, 0, 0, 0] + [0] * 54
                    buf = (ctypes.c_ubyte * 65)(*rep)
                    written = ctypes.wintypes.DWORD(0)
                    ok = k32.WriteFile(h, buf, 65, ctypes.byref(written), None)
                    k32.CloseHandle(h)
                    if ok:
                        return path
        except OSError:
            pass
        return None

    def __init__(self):
        self._lock = threading.RLock()
        self._held_mods = 0
        self._held_keys = set()
        self._btn_state = 0
        self._h = None
        self._k32 = ctypes.WinDLL('kernel32', use_last_error=True)
        self._k32.CreateFileW.restype = ctypes.wintypes.HANDLE
        self._k32.CreateFileW.argtypes = [ctypes.wintypes.LPCWSTR, ctypes.wintypes.DWORD, ctypes.wintypes.DWORD, ctypes.wintypes.LPVOID, ctypes.wintypes.DWORD, ctypes.wintypes.DWORD, ctypes.wintypes.HANDLE]
        self._k32.WriteFile.argtypes = [ctypes.wintypes.HANDLE, ctypes.wintypes.LPVOID, ctypes.wintypes.DWORD, ctypes.POINTER(ctypes.wintypes.DWORD), ctypes.wintypes.LPVOID]
        self._k32.WriteFile.restype = ctypes.wintypes.BOOL
        self._k32.CloseHandle.argtypes = [ctypes.wintypes.HANDLE]
        self._VK = dict(DD_VK)
        if not self._open():
            raise RuntimeError('备用驱动未就绪\n\n驱动未加载或未安装, 请切换回 KE Driver')
        return None

    def _open(self):
        path = self.find_col05()
        if not path:
            return False
        h = self._k32.CreateFileW(path, 1073741824, 3, None, 3, 0, None)
        if h in (None, -1, 0):
            return False
        self._h = h
        return True

    def _reopen(self):
        if self._h not in (None, -1, 0):
            try:
                self._k32.CloseHandle(self._h)
            except Exception:
                pass
        self._h = None
        return self._open()

    def _send(self, inner):
        rep = [64, len(inner)] + inner
        rep += [0] * (65 - len(rep))
        buf = (ctypes.c_ubyte * 65)(*rep)
        with self._lock as __temp_2906:
            for __temp_2908 in iter(range(2)):
                _ = __temp_2908
                w = ctypes.wintypes.DWORD(0)
                if self._k32.WriteFile(self._h, buf, 65, ctypes.byref(w), None):
                    return True
                err = ctypes.get_last_error()
                if not self._reopen():
                    print('[FakerInput] 写入失败: ' + str(hex(err)))
                    return False
                continue
        return False

    @staticmethod
    def _kbd_report(codes, flags):
        codes = (codes + [0] * 6)[slice(None, 6)]
        return [1, flags & 255, 0] + codes

    @staticmethod
    def _vk_to_hid(vk):
        if 65 <= vk:
            if vk <= 90:
                return ([vk - 61], 0)
        if 48 <= vk:
            if vk <= 57:
                return ([vk - 18], 0)
        if 112 <= vk:
            if vk <= 123:
                return ([vk - 54], 0)
        return ([], 0)

    def _key_to_hid(self, k):
        s = str(k).lower()
        if len(s) == 1:
            if s in _FI_CHARS:
                __temp_2928, __temp_2929 = _FI_CHARS[s]
                code = __temp_2928
                mod = __temp_2929
                if code:
                    return ([code], mod)
                else:
                    return ([], mod)
        if s in _FI_NAMES:
            __temp_2932, __temp_2933 = _FI_NAMES[s]
            code = __temp_2932
            mod = __temp_2933
            if code:
                return ([code], mod)
            else:
                return ([], mod)
        return self._vk_to_hid(self._VK.get(s, 0))

    def kd(self, k):
        __temp_2939, __temp_2940 = self._key_to_hid(k)
        codes = __temp_2939
        mod = __temp_2940
        if not codes:
            if not mod:
                print('[FakerInput] 未知键: ' + str(k))
                return None
        with self._lock as __temp_2942:
            if codes:
                self._held_keys |= set(codes)
                self._held_keys = self._held_keys
                self._send(self._kbd_report(sorted(self._held_keys), self._held_mods | mod))
                return None
            else:
                self._held_mods |= mod
                self._held_mods = self._held_mods
                self._send(self._kbd_report(sorted(self._held_keys), self._held_mods))
                return None
        return None

    def ku(self, k):
        __temp_2953, __temp_2954 = self._key_to_hid(k)
        codes = __temp_2953
        mod = __temp_2954
        if not codes:
            if not mod:
                return None
        with self._lock as __temp_2955:
            if codes:
                self._held_keys -= set(codes)
                self._held_keys = self._held_keys
                self._send(self._kbd_report(sorted(self._held_keys), self._held_mods))
                return None
            else:
                self._held_mods &= ~mod
                self._held_mods = self._held_mods
                self._send(self._kbd_report(sorted(self._held_keys), self._held_mods))
                return None
        return None

    def kp(self, k, ms=50):
        self.kd(k)
        if ms > 0:
            time.sleep(ms / 1000.0)
            self.ku(k)
            return None
        else:
            self.ku(k)
            return None

    def _set_btn(self, mask):
        self._btn_state = mask
        self._send([3, mask, 0, 0, 0, 0, 0, 0])
        return None

    def ml_d(self):
        self._set_btn(self._btn_state | 1)
        return None

    def ml_u(self):
        self._set_btn(self._btn_state & -2)
        return None

    def mr_d(self):
        self._set_btn(self._btn_state | 2)
        return None

    def mr_u(self):
        self._set_btn(self._btn_state & -3)
        return None

    def mm_d(self):
        self._set_btn(self._btn_state | 4)
        return None

    def mm_u(self):
        self._set_btn(self._btn_state & -5)
        return None

    def mm(self, ms=50):
        self.mm_d()
        if ms > 0:
            time.sleep(ms / 1000.0)
            self.mm_u()
            return None
        else:
            self.mm_u()
            return None

    def move_r(self, dx, dy):
        dx = max(-32767, min(32767, int(dx)))
        dy = max(-32767, min(32767, int(dy)))
        inner = [3, self._btn_state] + list(dx.to_bytes(2, 'little', signed=True)) + list(dy.to_bytes(2, 'little', signed=True)) + [0, 0]
        self._send(inner)
        return None

    def move_to(self, x, y):
        w = ctypes.windll.user32.GetSystemMetrics(0)
        h = ctypes.windll.user32.GetSystemMetrics(1)
        xv = max(0, min(32767, int(x) * 32767 // max(1, w)))
        yv = max(0, min(32767, int(y) * 32767 // max(1, h)))
        self._send([4, self._btn_state] + list(xv.to_bytes(2, 'little')) + list(yv.to_bytes(2, 'little')) + [0])
        return None

    def click(self):
        self.ml_d()
        time.sleep(0.03)
        self.ml_u()
        return None

    def scroll(self, delta):
        d = max(-127, min(127, int(delta)))
        self._send([3, self._btn_state, 0, 0, 0, 0, d & 255, 0])
        return None

    def release(self):
        try:
            with self._lock:
                self._btn_state = 0
                self._held_mods = 0
                self._held_keys.clear()
                self._send(self._kbd_report([], 0))
                self._send([3, 0, 0, 0, 0, 0, 0, 0])
        except Exception as exc:
            print('[FakerInput] 释放失败: ' + str(exc))

class ViiperInput:

    _API_PORT = 3242
    _MAGIC = b'eVI1\x00'
    _AUTH_CTX = b'VIIPER-Auth-v1'
    _SESS_CTX = b'VIIPER-Session-v1'
    _KEY_SALT = b'VIIPER-Key-v1'
    _ITER = 100000
    _NONCE_SZ = 32
    _key_cache = None
    _proc = None
    _from_meipass = False
    _ensure_lock = threading.Lock()

    @classmethod
    def stop_daemon(cls):
        proc = cls._proc
        cls._proc = None
        if proc is not None and proc.poll() is None:
            try:
                proc.terminate()
                try:
                    proc.wait(2)
                except Exception:
                    pass
            except Exception:
                pass

    def __init__(self):
        self._lock = threading.RLock()
        self._held_mods = 0
        self._held_keys = set()
        self._btn_state = 0
        self._bus = None
        self._kb_id = self._ms_id = None
        self._ekb = self._ems = None
        self._sock_kb = self._sock_ms = None
        self._last_move = 0.0
        self._reused = False
        self._warmup_done = False
        self._pw = self._read_password()
        if not self._ensure_server():
            raise RuntimeError('VIIPER 服务不可用\n\n请检查 usbip-win2 驱动是否安装，或切换回 KE Driver')
        try:
            if not self._setup_devices():
                raise RuntimeError('VIIPER 虚拟设备创建失败\n\n请检查 usbip-win2 驱动是否安装，或切换回 KE Driver')
            self._connect_streams()
        except Exception:
            self._cleanup()
            raise

    @staticmethod
    def _read_password():
        try:
            path = os.path.join(os.environ.get('APPDATA', ''), 'VIIPER', 'viiper.key.txt')
            with open(path, 'r', encoding='utf-8') as handle:
                return handle.read().strip() or None
        except Exception:
            return None

    @staticmethod
    def _find_viiper():
        launch_dir = os.path.dirname(os.path.abspath(sys.argv[0]))
        for base in (
            launch_dir,
            getattr(sys, '_MEIPASS', ''),
            os.path.dirname(os.path.abspath(__file__)),
            os.getcwd(),
        ):
            for candidate in (
                os.path.join(base, 'viiper.exe'),
                os.path.join(base, 'VIIPER', 'viiper.exe'),
                os.path.join(base, '资源', 'VIIPER', 'viiper.exe'),
            ):
                if candidate and os.path.isfile(candidate):
                    return candidate
        return None

    @classmethod
    def _ensure_persistent(cls, exe):
        if not getattr(sys, '_MEIPASS', None):
            cls._from_meipass = False
            return exe
        target_dir = os.path.join(os.environ.get('APPDATA', ''), 'VIIPER')
        target = os.path.join(target_dir, 'viiper.exe')
        try:
            os.makedirs(target_dir, exist_ok=True)
            if not os.path.isfile(target) or os.path.getsize(target) != os.path.getsize(exe):
                shutil.copy2(exe, target)
            cls._from_meipass = False
            return target
        except Exception:
            cls._from_meipass = True
            return exe

    @staticmethod
    def _viiper_running():
        try:
            class ProcessEntry(ctypes.Structure):
                _fields_ = [
                    ('dwSize', ctypes.c_uint32), ('cntUsage', ctypes.c_uint32),
                    ('th32ProcessID', ctypes.c_uint32), ('th32DefaultHeapID', ctypes.c_size_t),
                    ('th32ModuleID', ctypes.c_uint32), ('cntThreads', ctypes.c_uint32),
                    ('th32ParentProcessID', ctypes.c_uint32), ('pcPriClassBase', ctypes.c_long),
                    ('dwFlags', ctypes.c_uint32), ('szExeFile', ctypes.c_wchar * 260),
                ]
            k32 = ctypes.windll.kernel32
            snapshot = k32.CreateToolhelp32Snapshot(2, 0)
            if snapshot in (-1, 0):
                return False
            entry = ProcessEntry()
            entry.dwSize = ctypes.sizeof(ProcessEntry)
            found = False
            if k32.Process32FirstW(snapshot, ctypes.byref(entry)):
                while True:
                    if entry.szExeFile.lower() == 'viiper.exe':
                        found = True
                        break
                    if not k32.Process32NextW(snapshot, ctypes.byref(entry)):
                        break
            k32.CloseHandle(snapshot)
            return found
        except Exception:
            return False

    @staticmethod
    def _wait_port(port, timeout):
        import socket
        end = time.time() + timeout
        while time.time() < end:
            try:
                sock = socket.create_connection(('127.0.0.1', port), timeout=1.0)
                sock.close()
                return True
            except OSError:
                time.sleep(0.25)
        return False

    def _ensure_server_locked(self):
        import subprocess
        if self._wait_port(self._API_PORT, 0.3):
            if not self._pw:
                self._pw = self._read_password()
            return True
        exe = self._find_viiper()
        if not exe:
            return False
        if self._viiper_running():
            return self._wait_port(self._API_PORT, 5.0)
        exe = ViiperInput._ensure_persistent(exe)
        try:
            ViiperInput._proc = subprocess.Popen(
                [exe, '--usb.addr=127.0.0.1:3240', '--api.addr=127.0.0.1:3242',
                 '--api.device-handler-connect-timeout=1h', '--log.level=error'],
                creationflags=0x08000000,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )
        except Exception:
            return False
        if not self._wait_port(self._API_PORT, 5.0):
            return False
        if not self._pw:
            for _ in range(20):
                self._pw = self._read_password()
                if self._pw:
                    break
                time.sleep(0.25)
        return bool(self._pw)

    def _ensure_server(self):
        with ViiperInput._ensure_lock:
            return self._ensure_server_locked()

    def _handshake(self, sock):
        import hmac
        from Crypto.Cipher import ChaCha20_Poly1305
        cached = ViiperInput._key_cache
        if cached is None or cached[0] != self._pw:
            cached = (
                self._pw,
                hashlib.pbkdf2_hmac(
                    'sha256', self._pw.encode(), self._KEY_SALT,
                    self._ITER, 32,
                ),
            )
            ViiperInput._key_cache = cached
        key = cached[1]
        client_nonce = os.urandom(self._NONCE_SZ)
        auth_tag = hmac.new(
            key, self._AUTH_CTX + client_nonce, hashlib.sha256,
        ).digest()
        sock.sendall(self._MAGIC + client_nonce + auth_tag)
        response = b''
        wanted = 3 + self._NONCE_SZ
        while len(response) < wanted:
            chunk = sock.recv(4096)
            if not chunk:
                raise ConnectionError('连接无响应')
            response += chunk
        if not response.startswith(b'OK\x00'):
            raise RuntimeError('VIIPER 认证失败: %r' % response[:200])
        server_nonce = response[3:wanted]
        session_key = hashlib.sha256(
            key + server_nonce + client_nonce + self._SESS_CTX,
        ).digest()
        return self._EncSocket(sock, session_key)

    class _EncSocket:

        def __init__(self, sock, key):
            Crypto = __import__('Crypto.Cipher', fromlist=('ChaCha20_Poly1305',), level=0)
            ChaCha20_Poly1305 = Crypto.ChaCha20_Poly1305
            __temp_3105, __temp_3106, __temp_3107, __temp_3108 = (sock, key, 0, b'')
            self.sock = __temp_3105
            self.key = __temp_3106
            self.send_ctr = __temp_3107
            self.recv_buf = __temp_3108
            self._cipher = ChaCha20_Poly1305
            return None

        def send(self, data):
            struct = __import__('struct', fromlist=None, level=0)
            nonce = struct.pack('>Q', self.send_ctr) + b'\x00\x00\x00\x00'
            self.send_ctr += 1
            self.send_ctr = self.send_ctr
            c = self._cipher.new(key=self.key, nonce=nonce)
            __temp_3112, __temp_3113 = c.encrypt_and_digest(data)
            ct = __temp_3112
            tag = __temp_3113
            self.sock.sendall(struct.pack('>I', len(nonce) + len(ct) + len(tag)) + nonce + ct + tag)
            return None

        def recv_plain(self):
            import struct

            def exact(size):
                buf = b''
                while len(buf) < size:
                    chunk = self.sock.recv(size - len(buf))
                    if not chunk:
                        raise ConnectionError('连接已关闭')
                    buf += chunk
                return buf

            length = struct.unpack('>I', exact(4))[0]
            frame = exact(length)
            cipher = self._cipher.new(key=self.key, nonce=frame[:12])
            return cipher.decrypt_and_verify(frame[12:-16], frame[-16:])

    def _req(self, path, payload=''):
        socket = __import__('socket', fromlist=None, level=0)
        s = socket.create_connection(('127.0.0.1', self._API_PORT), timeout=30)
        es = self._handshake(s)
        if payload:
            line = path + (' ' + payload) + '\x00'
        else:
            line = path + '' + '\x00'
        es.send(line.encode())
        data = es.recv_plain()
        s.close()
        return data

    def _setup_devices(self):
        try:
            buses = json.loads(self._req('bus/list')).get('buses', []) or []
            for bus in buses:
                try:
                    devices = json.loads(self._req('bus/%d/list' % bus)).get('devices', [])
                    keyboards = [item for item in devices if item.get('type') == 'keyboard']
                    mice = [item for item in devices if item.get('type') == 'mouse']
                    if keyboards and mice and self._usbip_alive():
                        self._bus = bus
                        self._kb_id = keyboards[0]['devId']
                        self._ms_id = mice[0]['devId']
                        self._reused = True
                        return True
                except Exception:
                    continue
        except Exception:
            pass

        self._cleanup()
        print('[VIIPER] 无可复用设备，重建虚拟键盘和鼠标')
        result = json.loads(self._req('bus/create'))
        self._bus = result['busId']
        self._req('bus/%d/add' % self._bus, json.dumps({'type': 'keyboard'}))
        self._req('bus/%d/add' % self._bus, json.dumps({'type': 'mouse'}))
        devices = json.loads(self._req('bus/%d/list' % self._bus)).get('devices', [])
        keyboards = [item for item in devices if item.get('type') == 'keyboard']
        mice = [item for item in devices if item.get('type') == 'mouse']
        if not keyboards or not mice:
            return False
        self._kb_id = keyboards[0]['devId']
        self._ms_id = mice[0]['devId']
        return self._usbip_attach(self._kb_id) and self._usbip_attach(self._ms_id)

    @staticmethod
    def _usbip_alive():
        import subprocess
        try:
            output = subprocess.run(
                ['netstat', '-ano'], capture_output=True, text=True,
                timeout=5, creationflags=0x08000000,
            ).stdout
            return any(':3240' in line and 'ESTABLISHED' in line for line in output.splitlines())
        except Exception:
            return False

    def _usbip_attach(self, device_id):
        import subprocess
        exe = r'C:\Program Files\USBip\usbip.exe'
        if not os.path.isfile(exe):
            exe = shutil.which('usbip') or ''
        if not exe:
            return False
        try:
            result = subprocess.run(
                [exe, 'attach', '-r', '127.0.0.1', '-b',
                 '%d-%s' % (self._bus, device_id)],
                capture_output=True, text=True, encoding='utf-8',
                errors='replace', timeout=20,
            )
            return result.returncode == 0
        except Exception:
            return False

    def _connect_streams(self):
        socket = __import__('socket', fromlist=None, level=0)
        for __temp_3144 in iter(enumerate((('keyboard', '_sock_kb'), ('mouse', '_sock_ms')))):
            __temp_3145, __temp_3146 = __temp_3144
            i = __temp_3145
            __temp_3147, __temp_3148 = __temp_3146
            dev = __temp_3147
            attr = __temp_3148
            s = socket.create_connection(('127.0.0.1', self._API_PORT), timeout=30)
            es = self._handshake(s)
            if i == 0:
                es.send(('bus/%d/%s\x00' % (self._bus, getattr(self, '_kb_id'))).encode())
                setattr(self, attr, s)
            else:
                es.send(('bus/%d/%s\x00' % (self._bus, getattr(self, '_ms_id'))).encode())
                setattr(self, attr, s)
            if i == 0:
                setattr(self, '_ekb', es)
            else:
                setattr(self, '_ems', es)
            continue
        threading.Thread(target=self._warmup, daemon=True).start()
        return None

    def _warmup(self):
        if self._warmup_done:
            return None
        self._warmup_done = True
        warmup_count = 2 if self._reused else 3
        for __temp_3165 in range(warmup_count):
            _ = __temp_3165
            self._send_kb(0, [])
            self._send_ms(0)
            time.sleep(0.5)
            continue
        return None

    def _send_stream(self, kind, data):
        import socket
        for _ in range(2):
            try:
                getattr(self, '_e' + kind).send(data)
                return True
            except (ConnectionError, OSError):
                try:
                    sock = socket.create_connection(('127.0.0.1', self._API_PORT), timeout=2)
                    encrypted = self._handshake(sock)
                    device_id = self._kb_id if kind == 'kb' else self._ms_id
                    encrypted.send(('bus/%d/%s\x00' % (self._bus, device_id)).encode())
                    setattr(self, '_sock_' + kind, sock)
                    setattr(self, '_e' + kind, encrypted)
                    print('[VIIPER] %s 数据流断开，已重连' % kind)
                except Exception:
                    return False
        return False

    def _send_kb(self, mods, codes):
        if not self._warmup_done:
            self._warmup()
            codes = (codes + [0] * 6)[slice(None, 6)]
        else:
            codes = (codes + [0] * 6)[slice(None, 6)]
        return self._send_stream('kb', bytes([mods & 255, len(codes)]) + bytes(codes))

    def _send_ms(self, btn, dx=0, dy=0, wheel=0):
        if not self._warmup_done:
            self._warmup()
            struct = __import__('struct', fromlist=None, level=0)
        else:
            struct = __import__('struct', fromlist=None, level=0)
        return self._send_stream('ms', struct.pack('<Bhhhh', btn, dx, dy, wheel, 0))

    def _key_to_hid(self, k):
        s = str(k).lower()
        if len(s) == 1:
            if s in _FI_CHARS:
                __temp_3188, __temp_3189 = _FI_CHARS[s]
                code = __temp_3188
                mod = __temp_3189
                if code:
                    return ([code], mod)
                else:
                    return ([], mod)
        if s in _FI_NAMES:
            __temp_3192, __temp_3193 = _FI_NAMES[s]
            code = __temp_3192
            mod = __temp_3193
            if code:
                return ([code], mod)
            else:
                return ([], mod)
        vk = DD_VK.get(s, 0)
        if 65 <= vk:
            if vk <= 90:
                return ([vk - 61], 0)
        if 48 <= vk:
            if vk <= 57:
                return ([vk - 18], 0)
        if 112 <= vk:
            if vk <= 123:
                return ([vk - 54], 0)
        return ([], 0)

    def kd(self, k):
        __temp_3202, __temp_3203 = self._key_to_hid(k)
        codes = __temp_3202
        mod = __temp_3203
        if not codes:
            if not mod:
                print('[VIIPER] 未知键: ' + str(k))
                return None
        with self._lock as __temp_3205:
            if codes:
                self._held_keys |= set(codes)
                self._held_keys = self._held_keys
                self._send_kb(self._held_mods | mod, sorted(self._held_keys))
                return None
            else:
                self._held_mods |= mod
                self._held_mods = self._held_mods
                self._send_kb(self._held_mods, sorted(self._held_keys))
                return None
        return None

    def ku(self, k):
        __temp_3214, __temp_3215 = self._key_to_hid(k)
        codes = __temp_3214
        mod = __temp_3215
        if not codes:
            if not mod:
                return None
        with self._lock as __temp_3216:
            if codes:
                self._held_keys -= set(codes)
                self._held_keys = self._held_keys
                self._send_kb(self._held_mods, sorted(self._held_keys))
                return None
            else:
                self._held_mods &= ~mod
                self._held_mods = self._held_mods
                self._send_kb(self._held_mods, sorted(self._held_keys))
                return None
        return None

    def kp(self, k, ms=50):
        self.kd(k)
        if ms > 0:
            time.sleep(ms / 1000.0)
            self.ku(k)
            return None
        else:
            self.ku(k)
            return None

    def _set_btn(self, mask):
        with self._lock as __temp_3244:
            self._btn_state = mask
            self._send_ms(mask)
            return None
        return None

    def ml_d(self):
        self._set_btn(self._btn_state | 1)
        return None

    def ml_u(self):
        self._set_btn(self._btn_state & -2)
        return None

    def mr_d(self):
        self._set_btn(self._btn_state | 2)
        return None

    def mr_u(self):
        self._set_btn(self._btn_state & -3)
        return None

    def mm_d(self):
        self._set_btn(self._btn_state | 4)
        return None

    def mm_u(self):
        self._set_btn(self._btn_state & -5)
        return None

    def mm(self, ms=50):
        self.mm_d()
        if ms > 0:
            time.sleep(ms / 1000.0)
            self.mm_u()
            return None
        else:
            self.mm_u()
            return None

    def scroll(self, delta):
        with self._lock as __temp_3283:
            self._send_ms(self._btn_state, wheel=max(-32767, min(32767, int(delta))))
            return None
        return None

    def click(self):
        self.ml_d()
        time.sleep(0.03)
        self.ml_u()
        return None

    def type_text(self, text, press_ms=0.05, gap_ms=0.06):
        try:
            caps_lock = bool(ctypes.windll.user32.GetKeyState(20) & 1)
        except Exception:
            caps_lock = False
        chars = []
        for char in str(text):
            if char == ' ':
                chars.append((_FI_NAMES['space'][0], 0))
            elif 'a' <= char.lower() <= 'z':
                code, _ = _FI_CHARS[char.lower()]
                chars.append((code, (2 if char.isupper() else 0) ^ (2 if caps_lock else 0)))
            elif char in _FI_CHARS:
                chars.append(_FI_CHARS[char])
            else:
                print('[VIIPER] type_text 未映射字符: %r' % char)
                return False
        with self._lock:
            try:
                for code, shift in chars:
                    mods = self._held_mods | shift
                    if not self._send_kb(mods, sorted(self._held_keys) + [code]):
                        return False
                    time.sleep(press_ms)
                    if not self._send_kb(self._held_mods, sorted(self._held_keys)):
                        return False
                    time.sleep(gap_ms)
                return True
            finally:
                self._send_kb(self._held_mods, sorted(self._held_keys))

    def move_r(self, dx, dy):
        now = time.time()
        wait = self._last_move + 0.0005 - now
        if wait > 0:
            time.sleep(wait)
        with self._lock:
            self._last_move = time.time()
            dx = max(-32767, min(32767, int(dx)))
            dy = max(-32767, min(32767, int(dy)))
            self._send_ms(self._btn_state, dx, dy)

    def move_to(self, x, y, _check=True):
        x, y = int(x), int(y)
        try:
            with self._lock:
                ctypes.windll.user32.SetCursorPos(x, y)
                time.sleep(0.004)
                self.move_r(2, 2)
                if _check:
                    point = ctypes.wintypes.POINT()
                    ctypes.windll.user32.GetCursorPos(ctypes.byref(point))
                    return abs(point.x - x) <= 8 and abs(point.y - y) <= 8
                return True
        except Exception:
            return False

    def release(self):
        try:
            with self._lock:
                self._btn_state = 0
                self._send_ms(0)
                self._held_mods = 0
                self._held_keys.clear()
                self._send_kb(0, [])
        except Exception as exc:
            print('[VIIPER] release ' + str(exc))

    def _cleanup(self):
        if not self._pw:
            return
        try:
            for sock in (self._sock_kb, self._sock_ms):
                if sock:
                    try:
                        sock.close()
                    except Exception:
                        pass
            buses = json.loads(self._req('bus/list')).get('buses', []) or []
            for bus in buses:
                try:
                    devices = json.loads(self._req('bus/%d/list' % bus)).get('devices', []) or []
                    for device in devices:
                        try:
                            self._req('bus/%d/remove' % bus, device['devId'])
                        except Exception:
                            pass
                    self._req('bus/remove', str(bus))
                except Exception:
                    pass
        except Exception:
            pass
        self._bus = self._kb_id = self._ms_id = None

def _viper_l2_ude():
    import subprocess
    try:
        output = subprocess.run(
            ['pnputil', '/enum-devices', '/class', 'USB'],
            capture_output=True,
            text=True,
            encoding='gbk',
            errors='replace',
            timeout=20,
            creationflags=0x08000000,
        ).stdout
    except Exception:
        return (0, 0)
    started = 0
    malformed = 0
    current = ''
    state = ''
    for line in output.splitlines():
        value = line.strip()
        lowered = value.lower()
        if lowered.startswith('instance id:') or lowered.startswith('实例 id:'):
            current = value.split(':', 1)[1].strip()
            continue
        if lowered.startswith('status:') or lowered.startswith('状态:'):
            state = value.split(':', 1)[1].strip()
            if current.lower().startswith('root\\usb'):
                if state.lower().startswith('started') or state.lower().startswith('已启动'):
                    started += 1
                else:
                    malformed += 1
    return (started, malformed)

def _viper_l4_probe():
    import socket
    probe = ViiperInput.__new__(ViiperInput)
    probe._pw = ViiperInput._read_password()
    if not probe._pw:
        return (False, 'key 文件缺失')
    try:
        sock = socket.create_connection(('127.0.0.1', ViiperInput._API_PORT), timeout=10)
        encrypted = probe._handshake(sock)
        encrypted.send(b'bus/list\x00')
        encrypted.recv_plain()
        sock.close()
        return (True, '握手+查询 OK')
    except Exception as exc:
        return (False, str(exc)[:40])

def viper_health_report():
    import socket
    import subprocess
    details = {}
    usbip_exe = r'C:\Program Files\USBip\usbip.exe'
    usbip_ok = os.path.isfile(usbip_exe)
    details['l0'] = (usbip_ok, 'usbip.exe' if usbip_ok else 'usbip.exe 缺失')
    api_ok = False
    try:
        sock = socket.create_connection(('127.0.0.1', ViiperInput._API_PORT), timeout=2)
        sock.close()
        api_ok = True
    except OSError:
        pass
    details['l1'] = (api_ok, 'API 3242 可达' if api_ok else '守护未启')
    started, malformed = _viper_l2_ude()
    details['l2'] = (
        started > 0,
        '根设备 Started x%d，异常/停止 x%d' % (started, malformed),
    )
    established = 0
    try:
        output = subprocess.run(
            ['netstat', '-ano'], capture_output=True, text=True,
            timeout=5, creationflags=0x08000000,
        ).stdout
        established = sum(
            1 for line in output.splitlines()
            if ':3240' in line and 'ESTABLISHED' in line
        )
    except Exception:
        pass
    details['l3'] = (established > 0, '3240 ESTABLISHED x%d' % established)
    l4_ok, l4_message = _viper_l4_probe() if api_ok else (False, '跳过')
    details['l4'] = (l4_ok, l4_message)
    if not details['l0'][0] or started == 0:
        return (2, details)
    if not api_ok or established <= 0 or not l4_ok:
        return (1, details)
    return (0, details)
