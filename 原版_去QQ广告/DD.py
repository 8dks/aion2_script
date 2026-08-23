"""KE 外设桌面主程序。"""
from __future__ import annotations
import base64
import copy
import ctypes
import datetime
import hashlib
import json
import os
import queue
import random
import re
import shutil
import socket
import sys
import threading
import time
import urllib.request
import uuid
import webbrowser
import cv2
import dxcam
import numpy as np
from PIL import Image, ImageDraw, ImageGrab, ImageTk
import tkinter as tk
from tkinter import filedialog, messagebox, scrolledtext, simpledialog, ttk
import win32api
import win32con
import win32gui
import win32ui
from captcha_service import get_ai_state
from ke_engine import *
from ke_core import read_act_cache as _kc_rcache
from ke_core import verify_resp as _kc_verify
from ke_core import write_act_cache as _kc_wcache
import ke_sentinel
try:
    ctypes.windll.shcore.SetProcessDpiAwareness(2)
except Exception:
    try:
        ctypes.windll.user32.SetProcessDPIAware()
    except Exception:
        pass
_HWID_CACHE = ''
_EDIT_PWD = '860157'


def _sys_theme():
    try:
        import winreg
        with winreg.OpenKey(
            winreg.HKEY_CURRENT_USER,
            r'Software\Microsoft\Windows\CurrentVersion\Themes\Personalize',
        ) as key:
            light = winreg.QueryValueEx(key, 'AppsUseLightTheme')[0]
        return '原始粉' if light else '极墨'
    except Exception:
        return '原始粉'


POP_BG, POP_CARD, POP_BTN, POP_HV, POP_IN = (
    '#202020', '#2b2b2b', '#3a3a3a', '#4a4a4a', '#161b22'
)
POP_TXT, POP_SUB, POP_BTN_FG = '#c9d1d9', '#8b949e', '#ffffff'


def _refresh_pop():
    global POP_BG, POP_CARD, POP_BTN, POP_HV, POP_IN
    global POP_TXT, POP_SUB, POP_BTN_FG
    if _sys_theme() == '极墨':
        POP_BG, POP_CARD, POP_BTN, POP_HV, POP_IN = (
            '#202020', '#2b2b2b', '#3a3a3a', '#4a4a4a', '#161b22'
        )
        POP_TXT, POP_SUB, POP_BTN_FG = '#c9d1d9', '#8b949e', '#ffffff'
    else:
        POP_BG, POP_CARD, POP_BTN, POP_HV, POP_IN = (
            '#f0f0f0', '#ffffff', '#e0e0e0', '#d0d0d0', '#ffffff'
        )
        POP_TXT, POP_SUB, POP_BTN_FG = '#222222', '#666666', '#333333'
    try:
        App.POPUP.update(
            {
                'bg': POP_BG,
                'card': POP_CARD,
                'text': POP_TXT,
                'sub': POP_SUB,
                'entry_bg': POP_BG,
                'btn_fg': POP_BTN_FG,
                'hover': '#3a3a3a',
            }
        )
    except Exception:
        pass

def _prewarm_dxcam():
    try:
        camera = new_dxcam()
        if camera is not None:
            release_dxcam(camera)
    except Exception:
        pass

class App:
    _COLOR_WIN_THEME = {'bg': '#1e1e2e', 'row_bg': '#252530', 'txt': '#e0e0e0', 'sub': '#888', 'accent': '#4da6ff', 'del_btn': '#ef4444', 'del_hover': '#ff6b6b', 'det_btn': '#3b82f6', 'det_hover': '#5c9cff', 'det_active': '#FF9800', 'det_active_hover': '#FFB74D', 'new_btn': '#10b981', 'slider_trough': '#444'}
    POPUP = {'bg': '#161b22', 'card': '#1e2840', 'accent': '#58a6ff', 'text': '#c9d1d9', 'sub': '#8b949e', 'entry_bg': '#0d1117', 'btn_fg': 'white', 'hover': '#3b82f6'}
    _AI_COLORS = {'flash': '#f97316', 'ok': '#22c55e', 'fail': '#ef4444', 'idle': '#8b949e'}
    _mt_queue = queue.Queue()
    _act_srv_list = ['http://47.79.117.138:5888']
    _act_srv = load_settings().get('activate_server', '')
    if _act_srv and _act_srv not in _act_srv_list:
        _act_srv_list.insert(0, _act_srv)
    try:
        _socket = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        _socket.connect(('8.8.8.8', 80))
        _local = f'http://{_socket.getsockname()[0]}:5888'
        if _local not in _act_srv_list:
            _act_srv_list.append(_local)
        _socket.close()
    except Exception:
        pass
    _activation_settings = load_settings()
    _act_key = _activation_settings.get('activate_key', '')
    _act_ok = False
    _act_type = _activation_settings.get('activate_type', '')
    _act_exp = _activation_settings.get('activate_exp', '')
    _act_hwid = stable_hwid()
    _act_cache = os.path.join(SCRIPT_DIR, '激活缓存')

    def __init__(self):
        self.root = tk.Tk()
        self.root.title('K3M2 v26.8.21')
        self.root.resizable(True, True)
        self.root.configure(bg=POP_BG)
        self.settings = load_settings()
        geometry = self.settings.get('window_geo', '420x830+300+100')
        try:
            self.root.geometry(geometry)
        except Exception:
            self.root.geometry('420x830+300+100')
        self.root.minsize(420, 500)
        self._set_icon()
        self.runner = None
        self._active = False
        self._runner_thread = None
        self._current_script = None
        self._current_group = ''
        self._view_game = ''
        self._scripts = []
        self._closing = False
        self._starting = False
        self._running = False
        self._gen = 0
        self._ui_mem = None
        self._ui_mem_fail_ts = 0.0
        self._ui_mem_last_ok = 0.0
        self._mem_active = {}
        self._mem_timer = None
        self._detect_running = {}
        self._detect_stats = {}
        self._detect_timers = {}
        self._detect_busy = {}
        self._img_busy = {}
        self._helper_op = {}
        self._after_queue = queue.Queue()
        self._poll_after_timer = None
        self._drv_inst_cache = {}
        self._log_lock = threading.Lock()
        self._log_lines = []
        self._err_buf = []
        self._popup_windows = {}
        self._privacy_bar = None
        self._float = None
        self._pos_locked = bool(self.settings.get('float_locked', False))
        self._driver_mode = self.settings.get('input_mode', 'ttinput')
        self._macro_merge = self.settings.get('macro_merge', False)
        self._macro_fix_delay = self.settings.get('macro_fix_delay', False)
        try:
            self._macro_fix_delay_ms = int(float(self.settings.get('macro_fix_delay_ms', '0') or '0'))
        except Exception:
            self._macro_fix_delay_ms = 0
        threading.Thread(target=_prewarm_dxcam, daemon=True, name='dxcam_prewarm').start()
        self._merge_builtin_rules()
        self._build()
        self._apply_theme()
        self._float_win()
        self._refresh_list()
        self.root.after(600, self._show_privacy_bar)
        self._poll_after_timer = self.root.after(100, self._poll_after_queue)
        self.root.protocol('WM_DELETE_WINDOW', self._on_close)
        self._start_hotkey_thread()
        threading.Thread(target=self._auto_bind_loop, daemon=True, name='ke_auto_bind').start()
        threading.Thread(target=self._mem_viz_bg, daemon=True, name='ke_mem_viz').start()
        threading.Thread(target=self._check_driver, daemon=True).start()
        try:
            ke_sentinel.start(self)
        except Exception as exc:
            self._log(f'哨兵启动失败: {exc}')

    def _merge_builtin_rules(self):
        path = os.path.join(getattr(sys, '_MEIPASS', '') or '', '内置规则.dat')
        if not os.path.isfile(path):
            return
        try:
            rules = json.loads(lua_decrypt(open(path, 'rb').read()))
            added = 0
            for key in ('color_rules', 'color_thresholds', 'color_rules_enabled', 'img_rules_regions', 'img_thresholds', 'memory_rules'):
                for driver_name, values in (rules.get(key) or {}).items():
                    destination = self.settings.setdefault(key, {}).setdefault(driver_name, {})
                    for rule_name, rule_value in values.items():
                        if rule_name not in destination:
                            destination[rule_name] = rule_value
                            added += 1
            calibration = self.settings.setdefault('captcha_cal', {})
            for key, value in (rules.get('captcha_cal') or {}).items():
                if key not in calibration:
                    calibration[key] = value
                    added += 1
            if added:
                save_settings(self.settings)
                self._log(f'已内置作者规则: {added} 项(同名保留本地)')
        except Exception as exc:
            print(f'[内置规则] {exc}')

    def _set_icon(self):
        self._icon_path = None
        directories = [SCRIPT_DIR]
        if getattr(sys, '_MEIPASS', None):
            directories.insert(0, sys._MEIPASS)
        for directory in directories:
            path = os.path.join(directory, 'icon_pink.ico')
            if os.path.exists(path):
                try:
                    self.root.iconbitmap(default=path)
                    self._icon_path = path
                    return
                except Exception:
                    pass

    def _float_win(self):
        fw = tk.Toplevel(self.root)
        fw.overrideredirect(True)
        fw.attributes('-topmost', True)
        x = int(self.settings.get('float_x', 0) or 0)
        y = int(self.settings.get('float_y', 100) or 100)
        fw.configure(bg=POP_BG)
        initial_size = int(self.settings.get('float_size', 17) or 17)
        fw.geometry(f'{initial_size * 10 + 30}x{initial_size + 22}+{x}+{y}')
        bar = tk.Frame(fw, bg=POP_BG, cursor='hand2')
        bar.pack(fill='both', expand=True, padx=6, pady=(1, 3))
        self._float_lbl = tk.Label(
            bar,
            text='就绪',
            font=('Microsoft YaHei UI', 17, 'bold'),
            fg='#10b981',
            bg=POP_BG,
            cursor='hand2',
            anchor='center',
        )
        calibrate = tk.Label(
            bar,
            text='校准',
            font=('Microsoft YaHei UI', 8, 'bold'),
            bg=POP_BTN,
            fg=POP_BTN_FG,
            cursor='hand2',
            padx=4,
            pady=1,
        )
        calibrate.pack(side='right', padx=2)
        self._float_lbl.pack(
            side='left', fill='both', expand=True, padx=8, pady=(0, 1)
        )
        calibrate.bind(
            '<Button-1>', lambda _event: self._captcha_calibrate_manual()
        )
        font_size = self.settings.get('float_size')
        if font_size:
            self._float_lbl.config(
                font=('Microsoft YaHei UI', int(font_size), 'bold')
            )

        def start_drag(event):
            fw._dx, fw._dy = event.x, event.y
            fw._moved = False

        def move_drag(event):
            if getattr(self, '_pos_locked', False):
                return
            if abs(event.x - fw._dx) > 2 or abs(event.y - fw._dy) > 2:
                fw._moved = True
                fw.geometry(
                    f'+{fw.winfo_x() + event.x - fw._dx}'
                    f'+{fw.winfo_y() + event.y - fw._dy}'
                )

        def end_drag(_event):
            if fw._moved:
                px, py = fw.winfo_x(), fw.winfo_y()
                self.settings['float_x'] = px
                self.settings['float_y'] = py
                save_settings(self.settings)
                return
            self.root.deiconify()
            self.root.lift()
            self.root.focus_force()

        for widget in (bar, self._float_lbl):
            widget.bind('<ButtonPress-1>', start_drag)
            widget.bind('<B1-Motion>', move_drag)
            widget.bind('<ButtonRelease-1>', end_drag)
        self._float_lbl.bind('<Button-3>', lambda _event: self._on_close())
        self._fw = fw
        self._float = fw
        fw.deiconify()
        if not self.settings.get('float_show', True):
            fw.withdraw()

        self._focus_paused = False
        self._game_hwnd = self.settings.get('bind_hwnd', 0)
        try:
            if self._game_hwnd:
                self._log(
                    f"已绑定窗口: {self.settings.get('bind_title', '')} "
                    f'(hwnd={self._game_hwnd})'
                )
            else:
                self._log('未绑定窗口')
        except Exception:
            pass

        def poll_game_focus():
            if self._closing or not hasattr(self, '_active'):
                return
            try:
                self._game_hwnd = self.settings.get('bind_hwnd', 0)
                foreground = win32gui.GetForegroundWindow()
                simulator_title = self.settings.get('bind_title', '') or ''
                if (
                    '模拟器' in simulator_title
                    and self._game_hwnd
                    and not win32gui.IsWindow(self._game_hwnd)
                ):
                    try:
                        candidate = win32gui.GetForegroundWindow()
                        if candidate and not win32gui.IsIconic(candidate):
                            title = win32gui.GetWindowText(candidate)
                            rect = win32gui.GetWindowRect(candidate)
                            screen_width = win32api.GetSystemMetrics(0)
                            screen_height = win32api.GetSystemMetrics(1)
                            valid = bool(
                                title
                                and '模拟器' not in title
                                and 'K3M2' not in title
                                and 'KE外设' not in title
                                and '选择目标窗口' not in title
                                and rect[2] > rect[0]
                                and (rect[2] - rect[0]) * (rect[3] - rect[1])
                                >= 0.4 * screen_width * screen_height
                            )
                            if valid and getattr(self, '_sim_rebind_fg', 0) == candidate:
                                self._sim_rebind_n = getattr(self, '_sim_rebind_n', 0) + 1
                            else:
                                self._sim_rebind_fg = candidate if valid else 0
                                self._sim_rebind_n = 1 if valid else 0
                            if self._sim_rebind_n >= 3:
                                self.settings['bind_title'] = title
                                self.settings['bind_hwnd'] = candidate
                                save_settings(self.settings)
                                if hasattr(self, '_update_bind_title'):
                                    self._update_bind_title(title)
                                self._game_hwnd = candidate
                                self._sim_rebind_fg = 0
                                self._sim_rebind_n = 0
                                self._log(
                                    '[绑定] 模拟器测试结束, 已自动绑定游戏窗口: '
                                    + title
                                )
                    except Exception:
                        self._sim_rebind_fg = 0
                        self._sim_rebind_n = 0
                if not self._game_hwnd:
                    if not getattr(self, '_bind_warn_on', False):
                        self._bind_warn_start()
                    self.root.after(500, poll_game_focus)
                    return
                if getattr(self, '_bind_warn_on', False):
                    self._bind_warn_stop()
                is_game = foreground == self._game_hwnd
                if not is_game and foreground and self._game_hwnd:
                    try:
                        is_game = (
                            win32gui.GetWindowThreadProcessId(foreground)[1]
                            == win32gui.GetWindowThreadProcessId(self._game_hwnd)[1]
                        )
                    except Exception:
                        pass
                try:
                    if is_game and self._game_hwnd:
                        game_rect = win32gui.GetWindowRect(self._game_hwnd)
                        if game_rect[0] < -10000:
                            from ke_engine import restore_offscreen_window
                            restore_offscreen_window(self._game_hwnd)
                except Exception:
                    pass
                if self._active and not is_game and not self._focus_paused:
                    offscreen = None
                    try:
                        if self._game_hwnd:
                            game_rect = win32gui.GetWindowRect(self._game_hwnd)
                            offscreen = game_rect[0] < -10000
                    except Exception:
                        pass
                    if offscreen is False:
                        self._log('[暂停] 离开目标窗口')
                        self._stop()
                        self._focus_paused = True
                elif self._focus_paused and is_game:
                    self._focus_paused = False
                    self._log('[恢复] 回到目标窗口')
            except BaseException:
                pass
            self.root.after(500, poll_game_focus)

        def update_hwnd():
            if self._closing:
                return
            self._game_hwnd = self.settings.get('bind_hwnd', 0)
            self.root.after(2000, update_hwnd)

        self.root.after(1000, poll_game_focus)
        self.root.after(2000, update_hwnd)

    def _refresh_list(self):
        for child in self.script_list.get_children():
            self.script_list.delete(child)
        scripts = list_scripts()
        self._scripts = scripts

        def is_abyss(name):
            return name.startswith('深渊') or name in ('天族下层', '魔族下层')

        scripts.sort(key=lambda item: (is_abyss(item.get('name', '')), len(item.get('name', ''))))
        game_info = self.settings.get('game_info', {}) or {}
        groups = {}
        for script in scripts:
            groups.setdefault(script.get('game') or '未分类', []).append(script)
        for game_name in game_info:
            groups.setdefault(game_name, [])
        if self._view_game:
            groups = {key: value for key, value in groups.items() if key == self._view_game}
        for game_name in sorted(groups, key=lambda key: (not groups[key], key != '未分类' if groups[key] else False, key)):
            group_scripts = groups[game_name]
            group_id = '_g:' + game_name
            info = game_info.get(game_name, {}) or {}
            self.script_list.insert('', 'end', values=(info.get('type', ''), game_name, info.get('desc', '')), iid=group_id, tags=('game_group',))
            for script in group_scripts:
                name = script.get('name', '?')
                description = script.get('desc', '') if script.get('desc') != name else ''
                self.script_list.insert(group_id, 'end', values=('LUA', name, description), iid=script['file'])
            self.script_list.item(group_id, open=bool(self._view_game))
        self.script_list.tag_configure('game_group', font=('Microsoft YaHei UI', 10, 'bold'), foreground=self._t.get('gp_fg', '#cccccc'), background=self._t.get('gp_bg', '#1d242e'))
        last_script = self.settings.get('last_script', '') or self._current_script
        if last_script:
            try:
                if self.script_list.exists(last_script):
                    self.script_list.selection_set(last_script)
                    if self._view_game:
                        self.script_list.see(last_script)
                    self._current_script = last_script
            except Exception:
                pass

    def _game_manager(self):
        if self._popup_check('进程管理'):
            return
        palette = self.POPUP
        window = tk.Toplevel(self.root)
        window.title('进程管理')
        self._popup_register(window, '进程管理')
        self._popup_snap(window, '进程管理', 480, 430)
        window.configure(bg=palette['bg'])
        window.transient(self.root)
        tk.Label(window, text='已有分组(点击选中可编辑):', bg=palette['bg'], fg=palette['text'], font=('Microsoft YaHei UI', 10)).pack(anchor='w', padx=12, pady=(10, 2))
        group_list = tk.Listbox(window, height=8, bg=palette['entry_bg'], fg=palette['text'], relief='flat', font=('Microsoft YaHei UI', 10))
        group_list.pack(fill='x', padx=12)

        def fill():
            group_list.delete(0, 'end')
            for game_name, info in (self.settings.get('game_info', {}) or {}).items():
                info = info or {}
                group_list.insert('end', f"[{info.get('type', '')}] {game_name}  |  {info.get('desc', '')}")

        fill()
        tk.Label(window, text='分组名 / 类型 / 功能说明:', bg=palette['bg'], fg=palette['text'], font=('Microsoft YaHei UI', 10)).pack(anchor='w', padx=12, pady=(10, 2))
        entries = []
        for pady in (None, (4, 0), (4, 0)):
            entry = tk.Entry(window, bg=palette['entry_bg'], fg=palette['text'], insertbackground='#fff', relief='flat', font=('Microsoft YaHei UI', 10))
            options = {'fill': 'x', 'padx': 12}
            if pady is not None:
                options['pady'] = pady
            entry.pack(**options)
            entries.append(entry)
        name_entry, type_entry, desc_entry = entries

        def save():
            game_name = name_entry.get().strip()
            if not game_name:
                return
            self.settings.setdefault('game_info', {})[game_name] = {'type': type_entry.get().strip(), 'desc': desc_entry.get().strip()}
            save_settings(self.settings)
            fill()
            self._refresh_list()

        def select(_event=None):
            selection = group_list.curselection()
            if not selection:
                return
            game_name, info = list((self.settings.get('game_info', {}) or {}).items())[selection[0]]
            info = info or {}
            for entry, value in ((name_entry, game_name), (type_entry, info.get('type', '')), (desc_entry, info.get('desc', ''))):
                entry.delete(0, 'end')
                entry.insert(0, value)

        def remove():
            selection = group_list.curselection()
            if not selection:
                return
            game_name = list((self.settings.get('game_info', {}) or {}).keys())[selection[0]]
            self.settings.setdefault('game_info', {}).pop(game_name, None)
            save_settings(self.settings)
            if self._current_group == game_name:
                self._current_group = ''
            if self._view_game == game_name:
                self._view_game = ''
            fill()
            self._refresh_list()

        def new():
            for entry in entries:
                entry.delete(0, 'end')
            name_entry.focus_set()

        for entry in entries:
            entry.bind('<Return>', lambda _event: save())
        group_list.bind('<<ListboxSelect>>', select)
        buttons = tk.Frame(window, bg=palette['bg'])
        buttons.pack(fill='x', padx=12, pady=10)
        tk.Button(buttons, text='新建', command=new, bg=POP_BTN, fg='#fff', relief='flat', font=('Microsoft YaHei UI', 10)).pack(side='left')
        tk.Button(buttons, text='保存', command=save, bg=POP_BTN, fg='#fff', relief='flat', font=('Microsoft YaHei UI', 10)).pack(side='left', padx=4)
        tk.Button(buttons, text='移除', command=remove, bg='#E53935', fg='#fff', relief='flat', font=('Microsoft YaHei UI', 10)).pack(side='left', padx=4)
        tk.Button(buttons, text='关闭', command=window.destroy, bg=POP_BTN, fg='#fff', relief='flat', font=('Microsoft YaHei UI', 10)).pack(side='right')

    def _on_script_select(self, evt):
        selection = self.script_list.selection()
        if not selection:
            return
        file_name = selection[0]
        if file_name.startswith('_g:'):
            game_name = file_name[3:]
            self._current_group = game_name
            self._view_game = '' if self._view_game == game_name else game_name
            self._refresh_list()
            return
        scripts = {item['file']: item for item in list_scripts()}
        if file_name not in scripts:
            return
        self._current_script = file_name
        try:
            parent = self.script_list.parent(file_name)
            self._current_group = parent[3:] if parent.startswith('_g:') else ''
        except Exception:
            self._current_group = ''
        if self.settings.get('last_script') != file_name:
            self.settings['last_script'] = file_name
            save_settings(self.settings)
        self._stop_all_detect()
        for key, opener in (('色库', '_open_color_lib'), ('Mem Rules', '_open_mem_rules')):
            popup = getattr(self, '_popup_' + key, None)
            if popup and popup.winfo_exists():
                setattr(self, '_popup_' + key, None)
                popup.destroy()
                self.root.after(200, getattr(self, opener))
        import_popup = getattr(self, '_popup_导入规则', None)
        if import_popup and import_popup.winfo_exists():
            setattr(self, '_popup_导入规则', None)
            import_popup.destroy()
        if hasattr(self, '_fls_btn') and self._fls_btn:
            try:
                code = lua_read_text(os.path.join(SCRIPTS_DIR, file_name))
                enabled = '_fls = float_status' in code or 'local _fls' in code
                self._fls_btn.config(bg='#10b981' if enabled else '#E53935', text='悬浮显示已开' if enabled else '悬浮显示已关')
            except Exception:
                pass

    def _new_script(self):
        number = 1
        while os.path.exists(os.path.join(SCRIPTS_DIR, f'新建Lua{number}.lua')):
            number += 1
        name = f'新建Lua{number}'
        game = f'-- game {self._current_group}\n' if self._current_group else ''
        source = f'''-- KE Driver
-- name {name}
{game}-- 介绍: 自动化配置

local _fls = float_status

function on_start()
    _fls("启动", "#10b981")
    log("start")
end

function on_tick()
    -- 在此编写循环逻辑
end

function on_stop()
    _fls("已停止", "#94a3b8")
    log("stop")
end
'''
        path = os.path.join(SCRIPTS_DIR, name + '.lua')
        lua_write_text(path, source)
        self._current_script = os.path.basename(path)
        self._refresh_list()
        self._log(f'新建: {name}' + (f' → 分组[{self._current_group}]' if self._current_group else ''))

    def _import_script(self):
        path = filedialog.askopenfilename(filetypes=[('Lua', '*.lua')])
        if not path:
            return
        basename = os.path.basename(path)
        destination = os.path.join(SCRIPTS_DIR, basename)
        if os.path.exists(destination):
            settings = load_settings()
            driver_list = settings.get('driver_list', [])
            if basename in driver_list:
                driver_list.remove(basename)
                settings['driver_list'] = driver_list
                save_settings(settings)
                self.settings = load_settings()
            self._refresh_list()
            self._log(f'已恢复: {basename}')
            return

        shutil.copy2(path, destination)
        if self._current_group:
            original = lua_read_text(destination)
            lines = original.split('\n')
            has_group = False
            for index, line in enumerate(lines):
                if line.strip().startswith('-- game'):
                    lines[index] = f'-- game {self._current_group}'
                    has_group = True
            if not has_group:
                for index, line in enumerate(lines):
                    if line.strip().startswith('-- name'):
                        lines.insert(index + 1, f'-- game {self._current_group}')
                        break
                else:
                    lines.insert(0, f'-- game {self._current_group}')
            lua_write_text(destination, '\n'.join(lines))

        code = lua_read_text(destination)
        display_name = basename.replace('.lua', '')
        for line in code.split('\n'):
            if line.strip().startswith('-- name '):
                display_name = line.strip()[7:].strip()
                break
        battle_keys = ['has_target', 'burst', 'search_go', 'find_color', 'on_tick']
        if any(key in code for key in battle_keys) and '_fls' not in code:
            if 'function on_start()' in code:
                code = code.replace(
                    'function on_start()',
                    'local _fls = float_status\n\nfunction on_start()\n'
                    '    _fls("启动","#10b981")',
                    1,
                )
            else:
                code = 'local _fls = float_status\n' + code
            lua_write_text(destination, code)
            self._log(f'导入: {basename} → [{display_name}] (已注入悬浮)')
        else:
            self._log(f'导入: {basename} → [{display_name}]')
        self._refresh_list()

    def _export_script(self):
        if not self._current_script:
            return
        destination = filedialog.asksaveasfilename(parent=self.root, defaultextension='.lua', initialfile=self._current_script, filetypes=[('Lua 驱动', '*.lua')])
        if destination:
            shutil.copy2(os.path.join(SCRIPTS_DIR, self._current_script), destination)

    def _inject_fls(self):
        if not self._current_script:
            return
        path = os.path.join(SCRIPTS_DIR, self._current_script)
        source = lua_read_text(path)
        if '_fls' not in source and 'function on_start()' in source:
            source = source.replace('function on_start()', 'local _fls = float_status\n\nfunction on_start()\n    _fls("启动", "#10b981")', 1)
            lua_write_text(path, source)

    def _edit_script(self):
        if not self._current_script:
            self._alert('提示', '请先选择一个驱动')
            return
        password = simpledialog.askstring(
            '编辑授权',
            '请输入驱动编辑密码:',
            show='*',
            parent=self.root,
        )
        if password != _EDIT_PWD:
            if password is not None:
                self._alert('提示', '密码错误, 无法编辑')
            return

        path = os.path.join(SCRIPTS_DIR, self._current_script)
        try:
            source = lua_read_text(path)
        except Exception as exc:
            self._alert('打开失败', str(exc))
            return

        editor = tk.Toplevel(self.root)
        editor.title(f'编辑 - {self._current_script}')
        try:
            if self._icon_path:
                editor.iconbitmap(self._icon_path)
        except BaseException:
            pass
        x = max(0, self.root.winfo_x() - 860)
        y = max(0, self.root.winfo_y() + self.root.winfo_height() - 600)
        editor.geometry(f'860x600+{x}+{y}')
        editor.minsize(500, 300)
        editor.configure(bg=POP_BG)

        toolbar = tk.Frame(editor, bg=POP_CARD, height=32)
        toolbar.pack(fill='x')
        toolbar.pack_propagate(False)
        toolbar_actions = {}

        def toolbar_button(text, command):
            button = tk.Button(
                toolbar,
                text=text,
                command=command,
                bg=POP_CARD,
                fg=POP_TXT,
                activebackground=POP_BTN,
                activeforeground=POP_BTN_FG,
                relief='flat',
                bd=0,
                padx=8,
                pady=3,
                font=('Microsoft YaHei UI', 8, 'bold'),
                cursor='hand2',
            )
            button.pack(side='left', padx=1, pady=1)
            self._bind_hover(button, POP_CARD, POP_BTN)
            toolbar_actions[text] = button
            return button

        main = tk.Frame(editor, bg=POP_BG)
        main.pack(fill='both', expand=True)
        code_frame = tk.Frame(main, bg=POP_BG)
        code_frame.pack(fill='both', expand=True)
        line_numbers = tk.Text(
            code_frame,
            width=4,
            bg=POP_BG,
            fg=POP_SUB,
            font=('Consolas', 11),
            relief='flat',
            bd=0,
            padx=2,
            pady=2,
            wrap='none',
            state='disabled',
            takefocus=0,
        )
        line_numbers.pack(side='left', fill='y')
        text = tk.Text(
            code_frame,
            font=('Consolas', 11),
            bg=POP_CARD,
            fg=POP_TXT,
            insertbackground='#58a6ff',
            relief='flat',
            bd=0,
            padx=10,
            pady=2,
            wrap='none',
            undo=True,
            tabs=('4c',),
        )
        text.pack(side='left', fill='both', expand=True)
        scrollbar = tk.Scrollbar(code_frame, command=text.yview, width=10)
        scrollbar.pack(side='right', fill='y')

        def on_yview(first, last):
            scrollbar.set(first, last)
            try:
                line_numbers.yview_moveto(first)
            except Exception:
                pass

        text.configure(yscrollcommand=on_yview)
        text.insert('1.0', source)

        keywords = (
            'function', 'end', 'if', 'then', 'else', 'elseif', 'for',
            'while', 'do', 'repeat', 'until', 'return', 'local', 'break',
            'nil', 'true', 'false', 'and', 'or', 'not', 'in', 'goto',
        )
        text.tag_config('kw', foreground='#58a6ff')
        text.tag_config('cmt', foreground='#6a9955')
        text.tag_config('str', foreground='#f0a060')
        text.tag_config('find', background='#facc15', foreground='#111827')

        def draw_lines():
            count = int(text.index('end-1c').split('.')[0])
            current = int(text.index('insert').split('.')[0])
            numbers = '\n'.join(str(index) for index in range(1, count + 1))
            line_numbers.configure(state='normal')
            line_numbers.delete('1.0', 'end')
            line_numbers.insert('1.0', numbers)
            line_numbers.tag_add('current', f'{current}.0', f'{current}.end')
            line_numbers.tag_config(
                'current', foreground='#f59e0b', font=('Consolas', 11, 'bold')
            )
            line_numbers.configure(state='disabled')
            try:
                first = text.yview()[0]
                line_numbers.yview_moveto(first)
            except Exception:
                pass

        highlight_timer = [None]

        def highlight(_event=None):
            if highlight_timer[0]:
                try:
                    editor.after_cancel(highlight_timer[0])
                except Exception:
                    pass
            def apply():
                highlight_timer[0] = None
                for tag in ('kw', 'cmt', 'str'):
                    text.tag_remove(tag, '1.0', 'end')
                content = text.get('1.0', 'end-1c')
                protected = []
                for match in re.finditer(r'--[^\n]*', content):
                    start = f'1.0+{match.start()}c'
                    end = f'1.0+{match.end()}c'
                    text.tag_add('cmt', start, end)
                    protected.append((match.start(), match.end()))
                for match in re.finditer(r'"[^"]*"|\'[^\']*\'', content):
                    start = f'1.0+{match.start()}c'
                    end = f'1.0+{match.end()}c'
                    text.tag_add('str', start, end)
                    protected.append((match.start(), match.end()))
                for keyword in keywords:
                    for match in re.finditer(r'\b' + keyword + r'\b', content):
                        if any(a <= match.start() < b for a, b in protected):
                            continue
                        text.tag_add(
                            'kw',
                            f'1.0+{match.start()}c',
                            f'1.0+{match.end()}c',
                        )
                draw_lines()
                update_status()
            highlight_timer[0] = editor.after(60, apply)

        status_bar = tk.Frame(editor, bg=POP_CARD, height=22)
        status_bar.pack(side='bottom', fill='x')
        status_bar.pack_propagate(False)
        status_file = tk.Label(
            status_bar,
            text=f'📄 {self._current_script}',
            font=('Microsoft YaHei UI', 8),
            fg=POP_TXT,
            bg=POP_CARD,
            padx=6,
        )
        status_file.pack(side='left')
        status_modified = tk.Label(
            status_bar,
            text='',
            font=('Consolas', 8),
            fg='#f59e0b',
            bg=POP_CARD,
            padx=6,
        )
        status_modified.pack(side='left')
        status_position = tk.Label(
            status_bar,
            text='Ln 1, Col 0',
            font=('Consolas', 8),
            fg=POP_SUB,
            bg=POP_CARD,
            padx=6,
        )
        status_position.pack(side='right')

        def update_status(_event=None):
            try:
                line, column = text.index('insert').split('.')
                status_position.configure(text=f'Ln {line}, Col {column}')
            except Exception:
                pass

        def save():
            lua_write_text(path, text.get('1.0', 'end-1c'))
            self._log('已保存: ' + str(self._current_script))
            self._refresh_list()
            status_modified.configure(text='已保存', fg='#10b981')
            text.edit_modified(False)

        find_hits = []
        find_index = [0]

        def find_dialog():
            dialog = tk.Toplevel(editor)
            dialog.title('查找 / 替换')
            dialog.configure(bg=POP_BG)
            dialog.transient(editor)
            dialog.resizable(False, False)
            dialog.geometry(
                f'430x170+{editor.winfo_x() + 120}+{editor.winfo_y() + 80}'
            )
            find_var = tk.StringVar()
            replace_var = tk.StringVar()
            for row, (label_text, variable) in enumerate(
                (('查找:', find_var), ('替换:', replace_var))
            ):
                tk.Label(
                    dialog, text=label_text, bg=POP_BG, fg=POP_TXT
                ).grid(row=row, column=0, padx=8, pady=8, sticky='e')
                entry = tk.Entry(
                    dialog,
                    textvariable=variable,
                    width=34,
                    bg=POP_CARD,
                    fg=POP_TXT,
                    insertbackground=POP_TXT,
                    relief='flat',
                )
                entry.grid(row=row, column=1, columnspan=4, padx=8, pady=8)
                if row == 0:
                    entry.focus_set()

            def collect():
                text.tag_remove('find', '1.0', 'end')
                find_hits.clear()
                needle = find_var.get()
                if not needle:
                    return
                start = '1.0'
                while True:
                    found = text.search(
                        needle, start, stopindex='end', nocase=False
                    )
                    if not found:
                        break
                    end = f'{found}+{len(needle)}c'
                    find_hits.append((found, end))
                    text.tag_add('find', found, end)
                    start = end
                find_index[0] = 0

            def next_match():
                collect() if not find_hits else None
                if not find_hits:
                    return
                start, end = find_hits[find_index[0] % len(find_hits)]
                find_index[0] += 1
                text.tag_remove('sel', '1.0', 'end')
                text.tag_add('sel', start, end)
                text.mark_set('insert', end)
                text.see(start)
                update_status()

            def replace_one():
                if text.tag_ranges('sel'):
                    selected = text.get('sel.first', 'sel.last')
                    if selected == find_var.get():
                        text.delete('sel.first', 'sel.last')
                        text.insert('insert', replace_var.get())
                        find_hits.clear()
                        highlight()
                next_match()

            def replace_all():
                needle = find_var.get()
                if not needle:
                    return
                content = text.get('1.0', 'end-1c')
                content, count = re.subn(
                    re.escape(needle),
                    lambda _match: replace_var.get(),
                    content,
                )
                text.delete('1.0', 'end')
                text.insert('1.0', content)
                find_hits.clear()
                highlight()
                status_modified.configure(text=f'已替换 {count} 处')

            tk.Button(dialog, text='查找下一个', command=next_match).grid(
                row=2, column=1, padx=3, pady=10
            )
            tk.Button(dialog, text='替换', command=replace_one).grid(
                row=2, column=2, padx=3, pady=10
            )
            tk.Button(dialog, text='全部替换', command=replace_all).grid(
                row=2, column=3, padx=3, pady=10
            )
            tk.Button(dialog, text='关闭', command=dialog.destroy).grid(
                row=2, column=4, padx=3, pady=10
            )
            dialog.bind('<Return>', lambda _event: next_match())

        templates = {
            'on_tick框架': 'function on_tick()\n    -- 循环逻辑\nend',
            'on_start框架': 'function on_start()\n    _fls("启动","#10b981")\n    log("start")\nend',
            '色库检测': 'if check_saved_colors("规则名") then\n    log("检测到目标")\nend',
            '找图': 'local pos=find_img("图片名")\nif pos then\n    click_at(pos[1],pos[2])\nend',
            '连发按键': 'burst_keys("1,2,3,4,r")',
            '验证码': 'captcha_solve({alert=true,auto_submit=true})',
            '点击坐标': 'click_at(50,50,"left",30)',
            '悬浮状态': 'float_status("文字","#00BCD4")',
        }

        def insert_template(code):
            text.insert('insert', '\n' + code.strip() + '\n')
            highlight()

        template_button = tk.Menubutton(
            toolbar,
            text='📋 模板',
            font=('Microsoft YaHei UI', 8, 'bold'),
            bg=POP_CARD,
            fg=POP_TXT,
            activebackground=POP_BTN,
            activeforeground=POP_BTN_FG,
            relief='flat',
            cursor='hand2',
            padx=8,
            pady=3,
        )
        template_menu = tk.Menu(
            template_button,
            tearoff=False,
            bg=POP_CARD,
            fg=POP_TXT,
            activebackground=POP_BTN,
            font=('Microsoft YaHei UI', 9),
        )
        template_button.configure(menu=template_menu)
        for name, code in templates.items():
            template_menu.add_command(
                label=name, command=lambda value=code: insert_template(value)
            )

        log_frame = tk.Frame(main, bg='#161b22', height=180)
        log_text = tk.Text(
            log_frame,
            font=('Consolas', 9),
            bg='#161b22',
            fg='#c9d1d9',
            height=8,
            relief='flat',
            bd=0,
            padx=6,
            pady=4,
            wrap='word',
            state='disabled',
        )
        log_text.pack(fill='both', expand=True)
        log_visible = [False]

        def load_log():
            log_text.configure(state='normal')
            log_text.delete('1.0', 'end')
            with self._log_lock:
                lines = list(self._log_lines)
            log_text.insert('1.0', '\n'.join(str(line) for line in lines[-300:]))
            log_text.configure(state='disabled')
            log_text.see('end')

        def toggle_log():
            log_visible[0] = not log_visible[0]
            if log_visible[0]:
                log_frame.pack(side='bottom', fill='x')
                load_log()
            else:
                log_frame.pack_forget()

        toolbar_button('💾 保存', save)
        toolbar_button('🔍 查找', find_dialog)
        tk.Label(
            toolbar,
            text='|',
            fg='#3a3a3a',
            bg=POP_CARD,
            font=('Consolas', 10),
        ).pack(side='left', padx=4)
        template_button.pack(side='left', padx=1, pady=1)
        tk.Label(
            toolbar,
            text='|',
            fg='#3a3a3a',
            bg=POP_CARD,
            font=('Consolas', 10),
        ).pack(side='left', padx=4)
        toolbar_button('◫ 日志', toggle_log)
        toolbar_button('✕ 关闭', editor.destroy)

        def on_modified(_event=None):
            if text.edit_modified():
                status_modified.configure(text='● 已修改', fg='#f59e0b')
                text.edit_modified(False)
                highlight()

        editor.bind('<Control-s>', lambda _event: (save(), 'break')[1])
        editor.bind('<Control-f>', lambda _event: (find_dialog(), 'break')[1])
        editor.bind('<Control-w>', lambda _event: (editor.destroy(), 'break')[1])
        editor.bind('<Escape>', lambda _event: editor.destroy())
        text.bind('<<Modified>>', on_modified)
        text.bind('<KeyRelease>', lambda _event: (highlight(), update_status()))
        text.bind('<ButtonRelease-1>', update_status)
        text.bind('<MouseWheel>', lambda _event: editor.after_idle(draw_lines))
        text.focus_set()
        text.edit_modified(False)
        highlight()
        self._log('编辑: ' + str(self._current_script))

    def _delete_script(self):
        if not self._current_script:
            return
        if not messagebox.askyesno('删除驱动', f'确定删除 {self._current_script}？', parent=self.root):
            return
        path = os.path.join(SCRIPTS_DIR, self._current_script)
        try:
            os.remove(path)
        except Exception as exc:
            self._alert('删除失败', str(exc))
            return
        self._current_script = ''
        self._refresh_list()

    def _ask_string(self, parent, title, prompt, initialvalue=''):
        key = '中文输入对话框'
        if self._popup_check(key):
            return None
        window = tk.Toplevel(parent)
        window.title(title)
        window.resizable(False, False)
        window.transient(parent)
        window.configure(bg=self.POPUP['bg'])
        window.attributes('-topmost', True)
        self._popup_snap(window, key, 380, 180, lock_size=True)
        result = [None]
        tk.Label(window, text=prompt, bg=self.POPUP['bg'], fg=self.POPUP['text'], font=('Microsoft YaHei UI', 10)).pack(padx=20, pady=(22, 8))
        entry = tk.Entry(window, width=34, bg=self.POPUP['entry_bg'], fg=self.POPUP['text'], insertbackground=self.POPUP['accent'], relief='flat', font=('Microsoft YaHei UI', 11))
        entry.pack(fill='x', padx=24, ipady=5)
        entry.insert(0, initialvalue or '')
        entry.selection_range(0, 'end')
        entry.focus_set()

        def finish(value=None):
            result[0] = entry.get().strip() if value is True else None
            self._popup_windows.pop(key, None)
            try:
                window.destroy()
            except Exception:
                pass
        bar = tk.Frame(window, bg=self.POPUP['bg'])
        bar.pack(pady=16)
        tk.Button(bar, text='确定', command=lambda: finish(True), bg=self.POPUP['accent'], fg=self.POPUP['btn_fg'], relief='flat', padx=18, pady=4).pack(side='left', padx=5)
        tk.Button(bar, text='取消', command=finish, bg=self.POPUP['card'], fg=self.POPUP['sub'], relief='flat', padx=18, pady=4).pack(side='left', padx=5)
        self._popup_windows[key] = window
        window.protocol('WM_DELETE_WINDOW', finish)
        window.bind('<Return>', lambda _event: finish(True))
        window.bind('<Escape>', lambda _event: finish())
        window.grab_set()
        self.root.wait_window(window)
        return result[0]

    def _color_win_save_geo(self, w=None):
        window = w or getattr(self, '_color_window', None)
        if window:
            self.settings['color_window_geo'] = window.geometry()
            save_settings(self.settings)

    def _stop_detect(self, key):
        self._detect_running[key] = False

    def _stop_all_detect(self):
        try:
            for key in list(self._detect_running):
                self._stop_detect(key)
        except Exception:
            pass
        try:
            if getattr(self, '_mem_timer', None):
                self.root.after_cancel(self._mem_timer)
                self._mem_timer = None
        except Exception:
            pass
        try:
            if hasattr(self, '_mem_active'):
                self._mem_active.clear()
        except Exception:
            pass

    def _color_win_rename(self, old_name, w):
        name = self._ask_string(w, '重命名', '新名称', old_name)
        if not name or name == old_name or (not self._current_script):
            return
        changed = False
        for setting_key in ('color_rules', 'color_rules_enabled', 'color_thresholds'):
            rules = self.settings.setdefault(setting_key, {}).setdefault(self._current_script, {})
            if old_name in rules:
                rules[name] = rules.pop(old_name)
                changed = True
        if changed:
            save_settings(self.settings)
            self._refresh_lib_if_open()

    def _color_win_del_rule(self, name, w):
        if not self._current_script:
            return
        for setting_key in ('color_rules', 'color_rules_enabled', 'color_thresholds'):
            rules = self.settings.setdefault(setting_key, {}).setdefault(self._current_script, {})
            rules.pop(name, None)
        save_settings(self.settings)
        self._refresh_lib_if_open()

    def _color_win_new_rule(self, w):
        name = self._ask_string(w, '新建颜色规则', '规则名称')
        if not name or not self._current_script:
            return
        rules = self.settings.setdefault('color_rules', {}).setdefault(self._current_script, {})
        rules.setdefault(name, [make_color_rule(50, 50, [255, 255, 255])])
        save_settings(self.settings)
        self._refresh_lib_if_open()

    def _new_rule_menu(self, w):
        menu = tk.Menu(w, tearoff=False)
        menu.add_command(label='颜色规则', command=lambda: self._color_win_new_rule(w))
        menu.add_command(label='内存规则', command=lambda: self._new_mem_rule(w))
        try:
            menu.tk_popup(w.winfo_pointerx(), w.winfo_pointery())
        finally:
            menu.grab_release()

    def _new_mem_rule(self, w):
        name = self._ask_string(w, '新建内存规则', '规则名称')
        if not name or not self._current_script:
            return
        rules = self.settings.setdefault('memory_rules', {}).setdefault(self._current_script, {})
        rules.setdefault(name, {'base': 'main+0x0', 'offsets': [], 'type': 'i32', 'expect': {'nonzero': True}, 'enabled': False})
        save_settings(self.settings)
        self._refresh_lib_if_open()
        rebuild = getattr(self, '_mem_rules_rebuild', None)
        if callable(rebuild):
            rebuild()

    def _refresh_lib_if_open(self):
        window = getattr(self, '_color_window', None)
        if window and window.winfo_exists():
            rebuild = getattr(self, '_color_rebuild', None)
            if callable(rebuild):
                rebuild()
            else:
                window.destroy()
                self._open_color_lib()

    def _mem_edit_rule_dlg(self, parent, nm, rl, on_saved=None):
        window = tk.Toplevel(parent)
        window.title(f'内存规则 - {nm}')
        window.geometry('460x310')
        fields = {}
        for row, (key, label) in enumerate((('base', '基址'), ('offsets', '偏移(逗号分隔)'), ('type', '类型'), ('expect', '预期(JSON)'))):
            tk.Label(window, text=label).grid(row=row, column=0, sticky='e', padx=8, pady=8)
            entry = tk.Entry(window, width=38)
            value = rl.get(key, '')
            if key == 'offsets':
                value = ','.join((hex(int(item)) for item in value))
            elif key == 'expect':
                value = json.dumps(value, ensure_ascii=False)
            entry.insert(0, str(value))
            entry.grid(row=row, column=1, padx=8, pady=8)
            fields[key] = entry

        def save():
            try:
                offsets = [int(item.strip(), 0) for item in fields['offsets'].get().split(',') if item.strip()]
                expect = json.loads(fields['expect'].get() or '{}')
                rl.update(base=fields['base'].get(), offsets=offsets, type=fields['type'].get(), expect=expect)
                save_settings(self.settings)
                window.destroy()
                if on_saved:
                    on_saved()
            except Exception as exc:
                messagebox.showerror('保存失败', str(exc), parent=window)
        tk.Button(window, text='保存', command=save).grid(row=5, column=0, columnspan=2, pady=14)

    def _ui_mem_get(self):
        now = time.time()
        if self._ui_mem is None:
            if now - self._ui_mem_fail_ts < 5.0:
                return None
            hw = self.settings.get('bind_hwnd', 0)
            tt = self.settings.get('bind_title', '')
            if not hw:
                if not tt:
                    return None
            ke_mem = __import__('ke_mem', fromlist=('KeMem',), level=0)
            KeMem = ke_mem.KeMem
            _m = KeMem()
            ok = False
            if tt:
                ok = _m.attach_by_title(tt)
            if not ok:
                if hw:
                    ok = _m.attach_by_hwnd(hw)
            if not ok:
                _err_txt = _m.last_error_text
                _m.close()
                self._ui_mem_fail_ts = now
                if not getattr(self, '_ui_mem_silent', False):
                    self._ui_mem_silent = True
                    self._log('[Mem] 连接探测失败: ' + str(_err_txt) + ' (5s后自动再试, 恢复前静默)')
                return None
            self._ui_mem = _m
            self._ui_mem_last_ok = now
            if getattr(self, '_ui_mem_silent', False):
                self._ui_mem_silent = False
                self._log('[Mem] 连接已恢复 PID=' + str(_m.pid) + ' (' + str(_m.bits) + '位)')
            else:
                self._log('[Mem] 共享连接已建立 PID=' + str(_m.pid) + ' (' + str(_m.bits) + '位)')
        return self._ui_mem

    def _drop_ui_mem(self):
        try:
            if self._ui_mem:
                self._ui_mem.close()
        except Exception:
            pass
        self._ui_mem = None

    def _mem_viz_bg(self):
        while not self._closing:
            time.sleep(1.5)
            try:
                if not self._current_script:
                    continue
                rules = self.settings.get('memory_rules', {}).get(self._current_script, {})
                if not rules:
                    continue
                memory = self._ui_mem_get()
                if memory is None or not memory.attached:
                    continue
                from ke_engine import _mem_viz, _mem_viz_lock
                visible = {}
                for name, rule in rules.items():
                    if not rule.get('enabled', True):
                        continue
                    base = rule.get('base')
                    offsets = rule.get('offsets', [])
                    dtype = rule.get('type', 'i32')
                    value = memory.chain_read(base, offsets, dtype)
                    if value is None:
                        continue
                    address = f'{base} ' + ' '.join((f'[{int(offset):#x}]' for offset in offsets))
                    visible[name] = {'addr': address.strip(), 'value': value, 'expect': rule.get('expect'), 'hit': eval_expect(value, rule.get('expect')), 'ts': time.time()}
                with _mem_viz_lock:
                    _mem_viz['connected'] = True
                    _mem_viz['pid'] = memory.pid
                    _mem_viz['bits'] = memory.bits
                    _mem_viz['err'] = ''
                    _mem_viz['rules'] = visible
            except Exception:
                pass

    def _mem_loop(self):
        self._mem_timer = None
        if self._closing or not self._mem_active:
            return
        memory = self._ui_mem_get()
        for key, name in list(self._mem_active.items()):
            if not self._detect_running.get(key):
                self._mem_active.pop(key, None)
                continue
            stats = self._detect_stats.setdefault(key, {'total': 0, 'hits': 0})
            if memory is None:
                continue
            try:
                rule = self.settings.get('memory_rules', {}).get(self._current_script, {}).get(name, {})
                value = memory.chain_read(rule.get('base', ''), rule.get('offsets', []), rule.get('type', 'i32'))
                if value is not None:
                    self._ui_mem_last_ok = time.time()
                    stats['total'] += 1
                    stats['hits'] += int(eval_expect(value, rule.get('expect')))
                elif time.time() - self._ui_mem_last_ok > 10:
                    self._drop_ui_mem()
            except Exception:
                if time.time() - self._ui_mem_last_ok > 10:
                    self._drop_ui_mem()
        if self._mem_active:
            self._mem_timer = self._safe_after(300, self._mem_loop)

    def _test_mem_rule(self, name, key):
        if not self._detect_running.get(key):
            return
        if key not in self._mem_active:
            self._mem_active[key] = name
        if self._mem_timer is None:
            self._mem_timer = self._safe_after(300, self._mem_loop)

    def _test_img_rule(self, name, key=None):
        if key and self._img_busy.get(key):
            return
        if key:
            self._img_busy[key] = True

        def worker():
            error = None
            ok = False
            match_value = 0.0
            center_x = center_y = 0
            try:
                image_dir = os.path.join(SCRIPT_DIR, '图库')
                stem = os.path.splitext(name)[0]
                template_path = next((os.path.join(image_dir, filename) for filename in os.listdir(image_dir) if filename.lower().endswith(('.png', '.jpg', '.jpeg', '.bmp')) and os.path.splitext(filename)[0] == stem), None)
                if not template_path:
                    raise FileNotFoundError(f'{name}: 图库无此图片')
                template = cv2.imdecode(np.fromfile(template_path, dtype=np.uint8), cv2.IMREAD_UNCHANGED)
                if template is None:
                    raise ValueError(f'{name}: 模板读取失败')
                if template.ndim == 3 and template.shape[2] == 4:
                    template_bgr, template_mask = (template[:, :, :3], template[:, :, 3])
                else:
                    template_bgr = template if template.ndim == 3 else cv2.cvtColor(template, cv2.COLOR_GRAY2BGR)
                    template_mask = None
                screenshot = np.array(ImageGrab.grab().convert('RGB'))[:, :, ::-1]
                if template_bgr.shape[0] > screenshot.shape[0] or template_bgr.shape[1] > screenshot.shape[1]:
                    raise ValueError(f'{name}: 模板尺寸大于屏幕')
                if template_mask is not None:
                    result = cv2.matchTemplate(screenshot, template_bgr, cv2.TM_SQDIFF_NORMED, mask=template_mask)
                    minimum, _maximum, minimum_at, _maximum_at = cv2.minMaxLoc(result)
                    match_value = 1.0 - minimum
                    left, top = minimum_at
                else:
                    result = cv2.matchTemplate(screenshot, template_bgr, cv2.TM_CCOEFF_NORMED)
                    _minimum, match_value, _minimum_at, maximum_at = cv2.minMaxLoc(result)
                    left, top = maximum_at
                threshold = self.settings.get('img_thresholds', {}).get(self._current_script, {}).get(name, 100) / 100.0
                ok = match_value >= threshold
                center_x = left + template_bgr.shape[1] // 2
                center_y = top + template_bgr.shape[0] // 2
            except Exception as exc:
                error = str(exc)
            self._after_queue.put((self._img_apply, (name, key, ok, match_value, center_x, center_y, error)))
        threading.Thread(target=worker, daemon=True).start()

    def _img_apply(self, name, key, ok, mv, cx, cy, err):
        if key:
            self._img_busy.pop(key, None)
        if err:
            self._log(f'[图] {err}')
            return
        if key:
            if not self._detect_running.get(key):
                return
            stats = self._detect_stats.setdefault(key, {'total': 0, 'hits': 0})
            stats['total'] += 1
            stats['hits'] += int(bool(ok))
            attribute = '_last_img_ok_' + str(key)
            last = getattr(self, attribute, None)
            if ok != last:
                setattr(self, attribute, ok)
                self._log(f'[图] {name}: ✓ 已命中 ({round(mv * 100)}%)' if ok else f'[图] {name}: ✗ 丢失')
            return
        self._log(f"[图] {name}: 匹配度{round(mv * 100)}% {('命中' if ok else '未命中')} 中心@({cx},{cy})")

    def _backup_rules_to_server(self):
        if not self._current_script:
            self._log('请先选中一个驱动')
            return
        key = self.settings.get('activate_key', '')
        if not key:
            self._log('请先激活软件')
            return
        if getattr(self, '_backing_rules', False):
            self._log('备份中，请稍候')
            return
        script = self._current_script
        color_rules = self.settings.get('color_rules', {}).get(script, {})
        color_thresholds = self.settings.get('color_thresholds', {}).get(script, {})
        memory_rules = self.settings.get('memory_rules', {}).get(script, {})
        color_enabled = self.settings.get('color_rules_enabled', {}).get(script, {})
        image_enabled = self.settings.get('img_rules_enabled', {}).get(script, {})
        selected_stems = {os.path.splitext(filename)[0] for filename, enabled in image_enabled.items() if enabled}
        image_files = {}
        image_dir = os.path.join(SCRIPT_DIR, '图库')
        if os.path.isdir(image_dir):
            for filename in os.listdir(image_dir):
                if filename.lower().endswith(('.png', '.jpg', '.jpeg', '.bmp')) and os.path.splitext(filename)[0] in selected_stems:
                    try:
                        with open(os.path.join(image_dir, filename), 'rb') as stream:
                            image_files[filename] = base64.b64encode(stream.read()).decode()
                    except OSError:
                        pass
        image_thresholds = {filename: value for filename, value in self.settings.get('img_thresholds', {}).get(script, {}).items() if os.path.splitext(filename)[0] in selected_stems}
        image_regions = {name: value for name, value in self.settings.get('img_rules_regions', {}).get(script, {}).items() if name in selected_stems}
        payload = json.dumps({'key': key, 'script': script, 'rules': color_rules, 'thresholds': color_thresholds, 'color_rules': color_rules, 'color_thresholds': color_thresholds, 'memory_rules': memory_rules, 'img_files': image_files, 'color_rules_enabled': color_enabled, 'img_rules_enabled': image_enabled, 'img_thresholds': image_thresholds, 'img_rules_regions': image_regions}).encode()
        self._backing_rules = True

        def worker():
            try:
                server = self.settings.get('activate_server', 'http://47.79.117.138:5888')
                request = urllib.request.Request(f'{server}/rules/save', data=payload, headers={'Content-Type': 'application/json'})
                response = json.loads(urllib.request.urlopen(request, timeout=5).read())
                if response.get('ok'):
                    parts = [f'色{len(color_rules)}组', f'色阈值{len(color_thresholds)}', f'色勾选{len(color_enabled)}', f'M{len(memory_rules)}条', f'图{len(image_files)}张', f'图阈值{len(image_thresholds)}', f'图勾选{len(image_enabled)}', f'区域{len(image_regions)}']
                    if not image_files:
                        parts.append('⚠图库空(本次未备份图,恢复将无图)')
                    self._log('规则已备份: ' + ' | '.join(parts))
                else:
                    self._log(f"备份失败: {response.get('reason', '未知')}")
            except Exception as exc:
                self._log(f'备份失败: {exc}')
            finally:
                self._backing_rules = False
        threading.Thread(target=worker, daemon=True).start()

    def _restore_rules_from_server(self):
        if not self._current_script:
            self._log('请先选中一个驱动')
            return
        key = self.settings.get('activate_key', '')
        if not key:
            self._log('请先激活软件')
            return
        if getattr(self, '_restoring_rules', False):
            self._log('恢复中，请稍候')
            return
        script = self._current_script
        payload = json.dumps({'key': key, 'script': script}).encode()
        self._restoring_rules = True

        def worker():
            try:
                server = self.settings.get('activate_server', 'http://47.79.117.138:5888')
                request = urllib.request.Request(f'{server}/rules/load', data=payload, headers={'Content-Type': 'application/json'})
                response = json.loads(urllib.request.urlopen(request, timeout=5).read())
                if not response.get('ok'):
                    self._log(f"恢复失败: {response.get('reason', '服务器无备份')}")
                    return
                rules = response.get('color_rules', response.get('rules', {})) or {}
                thresholds = response.get('color_thresholds', {}) or {}
                memory_rules = response.get('memory_rules', {}) or {}
                images = response.get('img_files', {}) or {}
                image_thresholds = response.get('img_thresholds', {}) or {}
                image_regions = response.get('img_rules_regions', {}) or {}
                if not any((rules, memory_rules, images, image_regions)):
                    self._log('服务器无备份，未恢复任何规则')
                    return
                if rules:
                    self.settings.setdefault('color_rules', {})[script] = rules
                    enabled = self.settings.setdefault('color_rules_enabled', {}).setdefault(script, {})
                    saved_thresholds = self.settings.setdefault('color_thresholds', {}).setdefault(script, {})
                    for name in rules:
                        enabled[name] = False
                        saved_thresholds[name] = thresholds.get(name, 100)
                if memory_rules:
                    self.settings.setdefault('memory_rules', {})[script] = memory_rules
                    for rule in memory_rules.values():
                        if isinstance(rule, dict):
                            rule['enabled'] = False
                    self.settings.get('rules_deleted', {}).pop(script, None)
                if image_thresholds:
                    saved = self.settings.setdefault('img_thresholds', {}).setdefault(script, {})
                    image_enabled = self.settings.setdefault('img_rules_enabled', {}).setdefault(script, {})
                    for filename in image_thresholds:
                        saved[filename] = image_thresholds.get(filename, 95)
                        image_enabled[filename] = False
                if image_regions:
                    saved_regions = self.settings.setdefault('img_rules_regions', {}).setdefault(script, {})
                    for name, region in image_regions.items():
                        if isinstance(region, dict) and region.get('w_pct', 0) > 0:
                            saved_regions[name] = region
                image_dir = os.path.join(SCRIPT_DIR, '图库')
                os.makedirs(image_dir, exist_ok=True)
                restored_images = 0
                for filename, encoded in images.items():
                    safe_name = os.path.basename(str(filename))
                    if not safe_name.lower().endswith(('.png', '.jpg', '.jpeg', '.bmp')):
                        continue
                    try:
                        with open(os.path.join(image_dir, safe_name), 'wb') as stream:
                            stream.write(base64.b64decode(str(encoded)))
                        restored_images += 1
                    except Exception:
                        pass
                save_settings(self.settings)
                point_count = sum((len(value) for value in rules.values())) if isinstance(rules, dict) else 0
                self._log(f'规则已恢复: {point_count} 个色点 {len(rules)} 组, {len(memory_rules)} 条 Mem 规则, {restored_images} 张图片, {len(image_thresholds)} 组图阈值（√默认不勾，请自行确认）')
                self._after_queue.put((self._refresh_lib_if_open, ()))
            except Exception as exc:
                self._log(f'恢复失败: {exc}')
            finally:
                self._restoring_rules = False
        threading.Thread(target=worker, daemon=True).start()

    def _open_color_lib(self):
        if not self._current_script:
            self._alert('提示', '请先选择驱动')
            return
        key = '色库'
        if self._popup_check(key):
            window = self._popup_windows[key]
            window.lift()
            window.focus_force()
            return

        palette = {
            'bg': '#202020',
            'card': '#2b2b2b',
            'text': '#e0e0e0',
            'sub': '#888888',
            'accent': '#4da6ff',
            'image': '#4ade80',
            'memory': '#fb923c',
        }
        window = tk.Toplevel(self.root)
        window.title(f'色库 - {self._current_script}')
        window.configure(bg=palette['bg'])
        window.transient(self.root)
        geometry = self.settings.get('color_window_geo', '760x580')
        try:
            window.geometry(geometry)
        except Exception:
            window.geometry('760x580')
        window.minsize(557, 430)
        self._color_window = window
        self._popup_register(
            window,
            key,
            lambda: (self._color_win_save_geo(window), self._stop_all_detect()),
        )

        footer = tk.Frame(window, bg=palette['bg'])
        footer.pack(side='bottom', fill='x', padx=10, pady=(4, 6))
        canvas_wrap = tk.Frame(window, bg=palette['bg'])
        canvas_wrap.pack(fill='both', expand=True, padx=4, pady=4)
        canvas = tk.Canvas(
            canvas_wrap,
            bg=palette['bg'],
            highlightthickness=0,
            borderwidth=0,
        )
        scrollbar = tk.Scrollbar(canvas_wrap, command=canvas.yview, width=10)
        canvas.configure(yscrollcommand=scrollbar.set)
        scrollbar.pack(side='right', fill='y')
        canvas.pack(side='left', fill='both', expand=True)
        body = tk.Frame(canvas, bg=palette['bg'])
        body_id = canvas.create_window((0, 0), window=body, anchor='nw')

        def sync_scroll(_event=None):
            canvas.configure(scrollregion=canvas.bbox('all'))
            canvas.itemconfigure(body_id, width=max(1, canvas.winfo_width()))

        body.bind('<Configure>', sync_scroll)
        canvas.bind('<Configure>', sync_scroll)
        canvas.bind(
            '<MouseWheel>',
            lambda event: canvas.yview_scroll(int(-event.delta / 120), 'units'),
        )

        def save_switch(group_key, name, variable):
            self.settings.setdefault(group_key, {}).setdefault(
                self._current_script, {}
            )[name] = bool(variable.get())
            save_settings(self.settings)

        def threshold_control(parent, group_key, name, default, minimum):
            values = self.settings.setdefault(group_key, {}).setdefault(
                self._current_script, {}
            )
            variable = tk.IntVar(value=int(values.get(name, default)))
            holder = tk.Frame(parent, bg=palette['card'])
            label = tk.Label(
                holder,
                text=f'{variable.get()}%匹配度',
                bg=palette['card'],
                fg=palette['accent'],
                font=('Microsoft YaHei UI', 8, 'bold'),
                width=9,
            )
            label.pack(side='left')
            scale = tk.Scale(
                holder,
                from_=minimum,
                to=100,
                variable=variable,
                orient='horizontal',
                showvalue=False,
                length=48,
                width=10,
                sliderlength=14,
                resolution=1,
                bg=palette['card'],
                fg=palette['accent'],
                activebackground=palette['accent'],
                highlightthickness=0,
                troughcolor='#161b22',
                command=lambda value: label.configure(
                    text=f'{int(float(value))}%匹配度'
                ),
            )
            scale.pack(side='left')
            def persist(_event=None):
                values[name] = int(variable.get())
                save_settings(self.settings)
            scale.bind('<ButtonRelease-1>', persist)
            scale.bind('<KeyRelease>', persist)
            return holder

        def toggle_detection(kind, name, button):
            detect_key = f'{kind}:{name}'
            if self._detect_running.get(detect_key):
                self._stop_detect(detect_key)
                button.configure(text='检测', bg='#3a3a3a')
                return
            self._detect_running[detect_key] = True
            button.configure(text='停止', bg='#f59e0b')
            if kind == 'memory':
                self._test_mem_rule(name, detect_key)
                return

            def tick():
                if (
                    not self._detect_running.get(detect_key)
                    or not window.winfo_exists()
                ):
                    try:
                        button.configure(text='检测', bg='#3a3a3a')
                    except Exception:
                        pass
                    return
                if kind == 'color':
                    self._test_color_rule(name, detect_key)
                else:
                    self._test_img_rule(name, detect_key)
                self.root.after(450, tick)

            tick()

        def rename_mapping(old_name, setting_keys, title):
            new_name = self._ask_string(window, title, '新名称', old_name)
            if not new_name or new_name == old_name:
                return
            for setting_key in setting_keys:
                mapping = self.settings.setdefault(setting_key, {}).setdefault(
                    self._current_script, {}
                )
                if old_name in mapping:
                    mapping[new_name] = mapping.pop(old_name)
            save_settings(self.settings)
            rebuild()

        def delete_mapping(name, setting_keys, title):
            if not messagebox.askyesno(
                title, f'确定移除 {name}？', parent=window
            ):
                return
            self._stop_detect(f'color:{name}')
            self._stop_detect(f'image:{name}')
            self._stop_detect(f'memory:{name}')
            for setting_key in setting_keys:
                self.settings.setdefault(setting_key, {}).setdefault(
                    self._current_script, {}
                ).pop(name, None)
            if 'memory_rules' in setting_keys:
                self.settings.setdefault('rules_deleted', {}).setdefault(
                    self._current_script, {}
                )[name] = True
            save_settings(self.settings)
            rebuild()

        def action_button(parent, text, command, bg, fg='white', bold=False):
            return tk.Button(
                parent,
                text=text,
                command=command,
                bg=bg,
                fg=fg,
                activebackground=bg,
                activeforeground=fg,
                relief='flat',
                bd=0,
                font=('Microsoft YaHei UI', 8, 'bold' if bold else 'normal'),
                padx=10,
                pady=5,
                cursor='hand2',
            )

        def add_section(title, color, count, row_index):
            tk.Label(
                body,
                text=f'{title} ({count})',
                bg=palette['bg'],
                fg=color,
                font=('Microsoft YaHei UI', 9, 'bold'),
                anchor='w',
            ).grid(
                row=row_index,
                column=0,
                sticky='w',
                padx=4,
                pady=(4 if row_index == 0 else 12, 2),
            )
            return row_index + 1

        def color_hex(value):
            try:
                red, green, blue = (max(0, min(255, int(v))) for v in value[:3])
                return f'#{red:02x}{green:02x}{blue:02x}'
            except Exception:
                return '#333333'

        def rebuild():
            self._stop_all_detect()
            for child in body.winfo_children():
                child.destroy()
            script = self._current_script
            color_rules = self.settings.setdefault('color_rules', {}).setdefault(
                script, {}
            )
            color_enabled = self.settings.setdefault(
                'color_rules_enabled', {}
            ).setdefault(script, {})
            image_regions = self.settings.setdefault(
                'img_rules_regions', {}
            ).setdefault(script, {})
            image_thresholds = self.settings.setdefault(
                'img_thresholds', {}
            ).setdefault(script, {})
            image_enabled = self.settings.setdefault(
                'img_rules_enabled', {}
            ).setdefault(script, {})
            image_names = sorted(
                set(image_regions) | set(image_thresholds) | set(image_enabled)
            )
            memory_rules = self.settings.setdefault(
                'memory_rules', {}
            ).setdefault(script, {})

            row_index = add_section(
                '🎨 色规则', palette['accent'], f'{len(color_rules)}组', 0
            )
            if not color_rules:
                tk.Label(
                    body,
                    text='  暂无色规则（规则向导可添加）',
                    bg=palette['bg'],
                    fg=palette['sub'],
                    font=('Microsoft YaHei UI', 8),
                ).grid(row=row_index, column=0, sticky='w', padx=4, pady=4)
                row_index += 1
            for name, points in color_rules.items():
                row = tk.Frame(body, bg=palette['card'], height=51)
                row.grid(
                    row=row_index,
                    column=0,
                    sticky='ew',
                    padx=0,
                    pady=1,
                )
                row.grid_propagate(False)
                row.grid_columnconfigure(3, weight=1)
                enabled_var = tk.BooleanVar(
                    value=bool(color_enabled.get(name, True))
                )
                tk.Checkbutton(
                    row,
                    variable=enabled_var,
                    command=lambda n=name, v=enabled_var: save_switch(
                        'color_rules_enabled', n, v
                    ),
                    bg=palette['card'],
                    activebackground=palette['card'],
                    selectcolor=palette['card'],
                    fg=palette['accent'],
                    bd=0,
                ).grid(row=0, column=0, padx=(4, 0), pady=7)
                tk.Label(
                    row,
                    text=name,
                    bg=palette['card'],
                    fg=palette['text'],
                    font=('Microsoft YaHei UI', 9, 'bold'),
                    width=7,
                    anchor='w',
                ).grid(row=0, column=1, padx=(0, 2))
                swatches = tk.Frame(row, bg=palette['card'])
                swatches.grid(row=0, column=2, padx=2)
                for config in list(points)[:4]:
                    color = config.get('color', [80, 80, 80]) if isinstance(config, dict) else [80, 80, 80]
                    tk.Canvas(
                        swatches,
                        width=12,
                        height=16,
                        bg=color_hex(color),
                        highlightthickness=1,
                        highlightbackground='#555555',
                    ).pack(side='left', padx=1)
                threshold_control(
                    row, 'color_thresholds', name, 100, 10
                ).grid(row=0, column=3, padx=4)
                detect = action_button(row, '检测', None, '#3a3a3a')
                detect.configure(
                    command=lambda n=name, b=detect: toggle_detection(
                        'color', n, b
                    )
                )
                detect.grid(row=0, column=4, padx=1)
                action_button(
                    row,
                    '改名',
                    lambda n=name: rename_mapping(
                        n,
                        (
                            'color_rules',
                            'color_rules_enabled',
                            'color_thresholds',
                        ),
                        '颜色规则改名',
                    ),
                    POP_BTN,
                    POP_BTN_FG,
                ).grid(row=0, column=5, padx=1)
                action_button(
                    row,
                    '删除',
                    lambda n=name: delete_mapping(
                        n,
                        (
                            'color_rules',
                            'color_rules_enabled',
                            'color_thresholds',
                        ),
                        '移除颜色规则',
                    ),
                    '#ef4444',
                ).grid(row=0, column=6, padx=(1, 0))
                row_index += 1

            row_index = add_section(
                '🖼 图规则', palette['image'], f'{len(image_names)}张', row_index
            )
            if not image_names:
                tk.Label(
                    body,
                    text='  该驱动暂无图规则（取图向导可添加）',
                    bg=palette['bg'],
                    fg=palette['sub'],
                    font=('Microsoft YaHei UI', 8),
                ).grid(row=row_index, column=0, sticky='w', padx=4, pady=4)
                row_index += 1
            for name in image_names:
                row = tk.Frame(body, bg=palette['card'], height=51)
                row.grid(row=row_index, column=0, sticky='ew', pady=1)
                row.grid_propagate(False)
                row.grid_columnconfigure(2, weight=1)
                enabled_var = tk.BooleanVar(
                    value=bool(image_enabled.get(name, True))
                )
                tk.Checkbutton(
                    row,
                    variable=enabled_var,
                    command=lambda n=name, v=enabled_var: save_switch(
                        'img_rules_enabled', n, v
                    ),
                    bg=palette['card'],
                    activebackground=palette['card'],
                    selectcolor=palette['card'],
                    fg=palette['image'],
                    bd=0,
                ).grid(row=0, column=0, padx=(4, 0), pady=7)
                tk.Label(
                    row,
                    text=name,
                    bg=palette['card'],
                    fg=palette['text'],
                    font=('Microsoft YaHei UI', 9, 'bold'),
                    width=14,
                    anchor='w',
                ).grid(row=0, column=1, padx=2)
                threshold_control(
                    row, 'img_thresholds', name, 95, 50
                ).grid(row=0, column=2, padx=4)
                detect = action_button(row, '检测', None, '#3a3a3a')
                detect.configure(
                    command=lambda n=name, b=detect: toggle_detection(
                        'image', n, b
                    )
                )
                detect.grid(row=0, column=3, padx=1)
                action_button(
                    row,
                    '改名',
                    lambda n=name: rename_mapping(
                        n,
                        (
                            'img_rules_regions',
                            'img_thresholds',
                            'img_rules_enabled',
                        ),
                        '图规则改名',
                    ),
                    POP_BTN,
                    POP_BTN_FG,
                ).grid(row=0, column=4, padx=1)
                action_button(
                    row,
                    '删除',
                    lambda n=name: delete_mapping(
                        n,
                        (
                            'img_rules_regions',
                            'img_thresholds',
                            'img_rules_enabled',
                        ),
                        '移除图规则',
                    ),
                    '#ef4444',
                ).grid(row=0, column=5, padx=(1, 0))
                row_index += 1

            row_index = add_section(
                '🧠 M规则', palette['memory'], f'{len(memory_rules)}条', row_index
            )
            if not memory_rules:
                tk.Label(
                    body,
                    text='  暂无 M 规则',
                    bg=palette['bg'],
                    fg=palette['sub'],
                    font=('Microsoft YaHei UI', 8),
                ).grid(row=row_index, column=0, sticky='w', padx=4, pady=4)
                row_index += 1
            for name, rule in memory_rules.items():
                row = tk.Frame(body, bg=palette['card'], height=51)
                row.grid(row=row_index, column=0, sticky='ew', pady=1)
                row.grid_propagate(False)
                row.grid_columnconfigure(2, weight=1)
                enabled_var = tk.BooleanVar(
                    value=bool(rule.get('enabled', True))
                )
                def save_memory_switch(n=name, v=enabled_var):
                    memory_rules[n]['enabled'] = bool(v.get())
                    save_settings(self.settings)
                tk.Checkbutton(
                    row,
                    variable=enabled_var,
                    command=save_memory_switch,
                    bg=palette['card'],
                    activebackground=palette['card'],
                    selectcolor=palette['card'],
                    fg=palette['memory'],
                    bd=0,
                ).grid(row=0, column=0, padx=(4, 0), pady=7)
                tk.Label(
                    row,
                    text=name,
                    bg=palette['card'],
                    fg=palette['text'],
                    font=('Microsoft YaHei UI', 9, 'bold'),
                    width=10,
                    anchor='w',
                ).grid(row=0, column=1, padx=2)
                offsets = ','.join(
                    hex(int(value)) for value in rule.get('offsets', [])
                )
                tk.Label(
                    row,
                    text=f"{rule.get('base', '')} {offsets}".strip(),
                    bg=palette['card'],
                    fg=palette['sub'],
                    font=('Consolas', 8),
                    anchor='w',
                ).grid(row=0, column=2, sticky='ew', padx=4)
                detect = action_button(row, '检测', None, '#3a3a3a')
                detect.configure(
                    command=lambda n=name, b=detect: toggle_detection(
                        'memory', n, b
                    )
                )
                detect.grid(row=0, column=3, padx=1)
                action_button(
                    row,
                    '编辑',
                    lambda n=name, r=rule: self._mem_edit_rule_dlg(
                        window, n, r, rebuild
                    ),
                    '#3b82f6',
                ).grid(row=0, column=4, padx=1)
                action_button(
                    row,
                    '改名',
                    lambda n=name: rename_mapping(
                        n, ('memory_rules',), 'M规则改名'
                    ),
                    POP_BTN,
                    POP_BTN_FG,
                ).grid(row=0, column=5, padx=1)
                action_button(
                    row,
                    '删除',
                    lambda n=name: delete_mapping(
                        n, ('memory_rules',), '移除M规则'
                    ),
                    '#ef4444',
                ).grid(row=0, column=6, padx=(1, 0))
                row_index += 1
            body.grid_columnconfigure(0, weight=1)
            body.update_idletasks()
            sync_scroll()

        def delete_all():
            script = self._current_script
            memory_names = list(
                self.settings.get('memory_rules', {}).get(script, {})
            )
            if not messagebox.askyesno(
                '一键移除',
                '确定移除当前驱动的全部颜色、图片和内存规则？',
                parent=window,
            ):
                return
            self._stop_all_detect()
            for setting_key in (
                'color_rules',
                'color_rules_enabled',
                'color_thresholds',
                'img_rules_regions',
                'img_rules_enabled',
                'img_thresholds',
                'memory_rules',
            ):
                self.settings.setdefault(setting_key, {})[script] = {}
            deleted = self.settings.setdefault('rules_deleted', {}).setdefault(
                script, {}
            )
            for name in memory_names:
                deleted[name] = True
            save_settings(self.settings)
            rebuild()

        def footer_button(text, command, bg, fg, column, bold=False):
            button = tk.Button(
                footer,
                text=text,
                command=command,
                bg=bg,
                fg=fg,
                activebackground=bg,
                activeforeground=fg,
                relief='flat',
                bd=0,
                font=('Microsoft YaHei UI', 9, 'bold' if bold else 'normal'),
                padx=12,
                pady=4,
                cursor='hand2',
            )
            button.grid(row=0, column=column, sticky='ew', padx=4)
            footer.grid_columnconfigure(column, weight=1)
            return button

        footer_button(
            '+ 新建规则', lambda: self._new_rule_menu(window), '#3a3a3a', 'white', 0, True
        )
        footer_button(
            '⬆ 云端备份', self._backup_rules_to_server, POP_BTN, POP_BTN_FG, 1
        )
        footer_button(
            '⬇ 云端恢复', self._restore_rules_from_server, POP_BTN, POP_BTN_FG, 2
        )
        footer_button('✕ 一键移除', delete_all, '#ef4444', 'white', 3, True)
        self._color_rebuild = rebuild
        rebuild()

    def _open_mem_rules(self):
        if not self._current_script:
            self._alert('提示', '请先选中一个驱动')
            return
        key = 'Mem Rules'
        if self._popup_check(key):
            window = self._popup_windows[key]
            window.lift()
            window.focus_force()
            return

        window = tk.Toplevel(self.root)
        window.title(f'AI-Mem - {self._current_script}')
        window.configure(bg=POP_BG)
        window.attributes('-topmost', True)
        window.transient(self.root)
        self._popup_snap(window, key, 900, 560)
        window.minsize(760, 420)
        self._popup_register(window, key)
        window.grid_rowconfigure(0, weight=1)
        window.grid_columnconfigure(0, weight=1)

        panes = tk.PanedWindow(
            window,
            orient='horizontal',
            sashwidth=5,
            bg=POP_BG,
            bd=0,
            relief='flat',
        )
        panes.grid(row=0, column=0, sticky='nsew')

        left = tk.Frame(panes, bg=POP_BG)
        right = tk.PanedWindow(
            panes,
            orient='vertical',
            sashwidth=5,
            bg=POP_BG,
            bd=0,
            relief='flat',
        )
        panes.add(left, minsize=330, width=410)
        panes.add(right, minsize=380)

        tk.Label(
            left,
            text='📋 规则管理',
            bg=POP_CARD,
            fg='#facc15',
            font=('Microsoft YaHei UI', 11, 'bold'),
            anchor='w',
            padx=10,
            pady=4,
        ).pack(fill='x', padx=(8, 4), pady=(6, 2))

        manage_frame = tk.Frame(left, bg=POP_BG)
        manage_frame.pack(fill='both', expand=True, padx=(8, 4))
        manage_columns = ('value', 'address')
        manage_tree = ttk.Treeview(
            manage_frame,
            columns=manage_columns,
            show='tree headings',
            selectmode='browse',
        )
        manage_tree.heading('#0', text='规则名')
        manage_tree.heading('value', text='当前值')
        manage_tree.heading('address', text='地址信息')
        manage_tree.column('#0', width=125, anchor='center')
        manage_tree.column('value', width=90, anchor='center')
        manage_tree.column('address', width=180, anchor='w')
        manage_scroll = tk.Scrollbar(
            manage_frame, command=manage_tree.yview, width=10
        )
        manage_tree.configure(yscrollcommand=manage_scroll.set)
        manage_scroll.pack(side='right', fill='y')
        manage_tree.pack(side='left', fill='both', expand=True)

        toolbar = tk.Frame(left, bg=POP_BG)
        toolbar.pack(fill='x', padx=(8, 4), pady=(4, 8))

        mem_panel = tk.Frame(right, bg=POP_BG)
        captcha_panel = tk.Frame(right, bg=POP_BG)
        right.add(mem_panel, minsize=170, height=230)
        right.add(captcha_panel, minsize=150)

        mem_header = tk.Frame(mem_panel, bg=POP_CARD)
        mem_header.pack(fill='x', padx=(4, 8), pady=(6, 2))
        tk.Label(
            mem_header,
            text='🤖 Mem 规则实时检测',
            bg=POP_CARD,
            fg='#10b981',
            font=('Microsoft YaHei UI', 11, 'bold'),
            anchor='w',
        ).pack(side='left', padx=10, pady=4)
        connection = tk.Label(
            mem_header,
            text='未连接',
            bg=POP_CARD,
            fg='#f87171',
            font=('Microsoft YaHei UI', 9),
        )
        connection.pack(side='right', padx=10)

        live_frame = tk.Frame(mem_panel, bg=POP_BG)
        live_frame.pack(fill='both', expand=True, padx=(4, 8), pady=(0, 4))
        live_columns = ('address', 'value', 'expect', 'hit')
        live_tree = ttk.Treeview(
            live_frame,
            columns=live_columns,
            show='tree headings',
            selectmode='browse',
        )
        live_tree.heading('#0', text='规则名')
        live_tree.heading('address', text='地址链')
        live_tree.heading('value', text='当前值')
        live_tree.heading('expect', text='预期')
        live_tree.heading('hit', text='命中')
        live_tree.column('#0', width=140, anchor='center')
        live_tree.column('address', width=300, anchor='w')
        live_tree.column('value', width=100, anchor='center')
        live_tree.column('expect', width=130, anchor='center')
        live_tree.column('hit', width=65, anchor='center')
        live_y = tk.Scrollbar(live_frame, command=live_tree.yview, width=10)
        live_x = tk.Scrollbar(
            live_frame, command=live_tree.xview, orient='horizontal', width=10
        )
        live_tree.configure(
            yscrollcommand=live_y.set, xscrollcommand=live_x.set
        )
        live_y.pack(side='right', fill='y')
        live_x.pack(side='bottom', fill='x')
        live_tree.pack(fill='both', expand=True)

        captcha_header = tk.Frame(captcha_panel, bg=POP_CARD)
        captcha_header.pack(fill='x', padx=(4, 8), pady=(2, 2))
        tk.Label(
            captcha_header,
            text='📷 验证码 AI 实时画面',
            bg=POP_CARD,
            fg='#06b6d4',
            font=('Microsoft YaHei UI', 11, 'bold'),
            anchor='w',
        ).pack(side='left', padx=10, pady=4)
        captcha_status = tk.Label(
            captcha_header,
            text='等待验证码',
            bg=POP_CARD,
            fg=POP_SUB,
            font=('Microsoft YaHei UI', 8),
        )
        captcha_status.pack(side='right', padx=10)
        preview = tk.Label(
            captcha_panel,
            text='实时画面准备中…',
            bg='#111827',
            fg='#9ca3af',
            font=('Microsoft YaHei UI', 10),
        )
        preview.pack(fill='both', expand=True, padx=(4, 8), pady=(0, 6))

        def rules():
            return self.settings.setdefault('memory_rules', {}).setdefault(
                self._current_script, {}
            )

        def expected_text(value):
            if not isinstance(value, dict):
                return str(value)
            if 'nonzero' in value:
                return '!=0'
            if 'range' in value:
                return str(value['range'])
            if 'value' in value:
                return f"{value.get('op', '==')}{value['value']}"
            return json.dumps(value, ensure_ascii=False)

        def selected_name():
            selection = manage_tree.selection()
            return selection[0] if selection else ''

        def rebuild():
            selected = selected_name()
            visual = get_mem_viz()
            current = visual.get('rules', {})
            manage_tree.delete(*manage_tree.get_children())
            for name, rule in rules().items():
                value_info = current.get(name, {})
                offsets = ' '.join(
                    f'[{int(item):#x}]' for item in rule.get('offsets', [])
                )
                address = f"{rule.get('base', '')} {offsets}".strip()
                state = '√' if rule.get('enabled', True) else '—'
                manage_tree.insert(
                    '',
                    'end',
                    iid=name,
                    text=f'{state} {name}',
                    values=(value_info.get('value', '—'), address),
                )
            if selected and manage_tree.exists(selected):
                manage_tree.selection_set(selected)

        def refresh_live():
            visual = get_mem_viz()
            connected = bool(visual.get('connected'))
            connection.configure(
                text=(
                    f"已连接 PID={visual.get('pid', 0)} "
                    f"({visual.get('bits', 0)}位)"
                    if connected
                    else visual.get('err') or '未连接'
                ),
                fg='#4ade80' if connected else '#f87171',
            )
            live_tree.delete(*live_tree.get_children())
            current = visual.get('rules', {})
            for name, rule in rules().items():
                value_info = current.get(name, {})
                offsets = ' '.join(
                    f'[{int(item):#x}]' for item in rule.get('offsets', [])
                )
                address = f"{rule.get('base', '')} {offsets}".strip()
                live_tree.insert(
                    '',
                    'end',
                    iid=name,
                    text=name,
                    values=(
                        address,
                        value_info.get('value', '—'),
                        expected_text(rule.get('expect', {})),
                        '✓' if value_info.get('hit') else (
                            '✗' if value_info else '—'
                        ),
                    ),
                )

        def new_rule():
            name = self._ask_string(window, '新建内存规则', '规则名称')
            if not name:
                return
            rule = rules().setdefault(
                name,
                {
                    'base': 'main+0x0',
                    'offsets': [],
                    'type': 'i32',
                    'expect': {'nonzero': True},
                    'enabled': False,
                },
            )
            save_settings(self.settings)
            self._mem_edit_rule_dlg(window, name, rule, rebuild)

        def edit_rule():
            name = selected_name()
            if name in rules():
                self._mem_edit_rule_dlg(window, name, rules()[name], rebuild)

        def toggle_rule():
            name = selected_name()
            if name in rules():
                rules()[name]['enabled'] = not rules()[name].get(
                    'enabled', True
                )
                save_settings(self.settings)
                rebuild()

        def test_rule():
            name = selected_name()
            rule = rules().get(name)
            memory = self._ui_mem_get()
            if not rule or memory is None:
                self._log(f"[Mem] {name or '规则'}: offline")
                return
            value = memory.chain_read(
                rule.get('base'),
                rule.get('offsets', []),
                rule.get('type', 'i32'),
            )
            hit = value is not None and eval_expect(
                value, rule.get('expect', {})
            )
            self._log(
                f"[Mem] {name}: {value if value is not None else 'N/A'} "
                f"{'✓' if hit else '✗'}"
            )

        def rename_rule():
            name = selected_name()
            if not name:
                return
            new_name = self._ask_string(window, '规则改名', '新名称', name)
            if not new_name or new_name == name:
                return
            rules()[new_name] = rules().pop(name)
            save_settings(self.settings)
            rebuild()

        def delete_rule():
            name = selected_name()
            if not name or not messagebox.askyesno(
                '删除规则', f'确定删除 {name}？', parent=window
            ):
                return
            rules().pop(name, None)
            self.settings.setdefault('rules_deleted', {}).setdefault(
                self._current_script, {}
            )[name] = True
            save_settings(self.settings)
            rebuild()

        def tool_button(text, command, color):
            tk.Button(
                toolbar,
                text=text,
                command=command,
                bg=color,
                fg='white',
                relief='flat',
                bd=0,
                padx=7,
                pady=3,
                font=('Microsoft YaHei UI', 8),
            ).pack(side='left', padx=2)

        tool_button('新建', new_rule, '#10b981')
        tool_button('编辑', edit_rule, '#3b82f6')
        tool_button('启用/停用', toggle_rule, '#6366f1')
        tool_button('测试', test_rule, '#f59e0b')
        tool_button('改名', rename_rule, '#64748b')
        tool_button('删除', delete_rule, '#ef4444')
        manage_tree.bind('<Double-1>', lambda _event: edit_rule())
        self._mem_rules_rebuild = rebuild

        preview_busy = [False]

        def apply_preview(image):
            preview_busy[0] = False
            if not window.winfo_exists():
                return
            try:
                width = max(200, preview.winfo_width())
                height = max(120, preview.winfo_height())
                source_width, source_height = image.size
                ratio = min(width / source_width, height / source_height)
                size = (
                    max(1, int(source_width * ratio)),
                    max(1, int(source_height * ratio)),
                )
                image = image.resize(size, Image.Resampling.LANCZOS)
                photo = ImageTk.PhotoImage(image)
                preview.configure(image=photo, text='')
                preview.image = photo
            except Exception:
                pass

        def capture_preview(state):
            try:
                image = ImageGrab.grab().convert('RGB')
                box = state.get('box')
                if box and len(box) == 4:
                    draw = ImageDraw.Draw(image)
                    draw.rectangle(tuple(box), outline='#00ff66', width=4)
                self._safe_after(0, apply_preview, image)
            except Exception:
                preview_busy[0] = False

        def tick():
            if not window.winfo_exists():
                return
            try:
                state = get_ai_state()
                status = state.get('status') or '等待验证码'
                answer = state.get('answer') or ''
                captcha_status.configure(
                    text=f'{status}{(" · " + answer) if answer else ""}',
                    fg=(
                        '#22c55e'
                        if '通过' in status or '已识别' in status
                        else '#ef4444' if '失败' in status else POP_SUB
                    ),
                )
                rebuild()
                refresh_live()
                if not preview_busy[0]:
                    preview_busy[0] = True
                    threading.Thread(
                        target=capture_preview,
                        args=(state,),
                        daemon=True,
                        name='ai_mem_preview',
                    ).start()
            except Exception:
                pass
            window.after(900, tick)

        rebuild()
        refresh_live()
        window.after(100, tick)

    def _ai_train(self):
        self._log('开始训练验证码模型')

        def worker():
            try:
                from captcha_ai_train import train_mlp
                accuracy = train_mlp(save_dir=SCRIPT_DIR)
                self._after_queue.put((self._alert, ('训练完成', f'准确率: {accuracy}')))
            except Exception as exc:
                self._after_queue.put((self._alert, ('训练失败', str(exc))))
        threading.Thread(target=worker, daemon=True).start()

    def _mem_bg_scan(self):
        memory = self._ui_mem_get()
        if not memory:
            self._alert('内存扫描', '请先绑定并启动游戏')
            return
        state = {'stop': False, 'memory': memory}
        threading.Thread(target=self._mem_bg_loop, args=(state,), daemon=True).start()

    def _mem_bg_loop(self, st):
        try:
            memory = st['memory']
            base = memory.module_base()
            if not base:
                raise RuntimeError('目标模块未加载')
            requested = int(self.settings.get('mem_scan_size', 524288) or 524288)
            scan_size = max(65536, min(requested, 8 * 1024 * 1024))
            raw = memory._rpm(base, scan_size)
            if not raw:
                raise RuntimeError('无可读数据区')
            baseline = {offset: int.from_bytes(raw[offset:offset + 4], 'little', signed=True) for offset in range(0, len(raw) - 3, 4)}
            st.update(base=base, scan_size=len(raw), base0=baseline, changed=[], ready=True)
            self._log(f'[Mem监控] 基线就绪 {len(baseline)}个i32')
            while not st.get('stop') and (not self._closing):
                time.sleep(1)
                current_raw = memory._rpm(base, len(raw))
                if not current_raw:
                    st['conn_err'] = memory.last_error_text or '读取失败'
                    continue
                changed = []
                for offset, old_value in baseline.items():
                    value = int.from_bytes(current_raw[offset:offset + 4], 'little', signed=True)
                    if value != old_value:
                        changed.append((base + offset, old_value, value))
                st['changed'] = changed
                history = st.setdefault('change_hist', [])
                history.append(changed)
                del history[:-3]
        except Exception as exc:
            st['conn_err'] = str(exc)
            self._log(f'[Mem监控] 失败: {exc}')
        finally:
            st['done'] = True

    def _auto_snap_phase1(self, st):
        if not st.get('ready'):
            self._log('[Mem自动采集] 基线尚未就绪')
            return
        addresses = {}
        for changes in st.get('change_hist', []):
            for address, old_value, value in changes:
                addresses[address] = (old_value, value)
        if not addresses:
            self._log('[Mem自动采集] 弹码但未捕获到变化，本次跳过')
            return
        memory = st['memory']
        snapshot = {}
        for address, (old_value, _value) in addresses.items():
            raw = memory._rpm(address, 4)
            if raw and len(raw) == 4:
                snapshot[address] = (old_value, int.from_bytes(raw, 'little', signed=True))
        st['snap1'] = snapshot
        st['collecting'] = True
        self._log(f'[Mem自动采集] ① 弹码已记录 {len(snapshot)} 个变化地址, 关码后点②')

    def _auto_snap_phase2(self, st):
        snapshot = st.get('snap1') or {}
        if not snapshot:
            self._log('[Mem自动采集] 请先执行①记录弹码')
            return
        memory = st['memory']
        candidates = []
        unreadable = 0
        for address, (baseline, active_value) in snapshot.items():
            raw = memory._rpm(address, 4)
            if not raw or len(raw) != 4:
                unreadable += 1
                continue
            current = int.from_bytes(raw, 'little', signed=True)
            if active_value != baseline and current == baseline:
                candidates.append((address, baseline, active_value, current))
        st['collecting'] = False
        st['results'] = candidates
        if not candidates:
            detail = f'，{unreadable} 个地址不可读' if unreadable else ''
            self._log(f'[Mem自动采集] ② 未找到回落地址{detail}')
            return
        rules = self.settings.setdefault('memory_rules', {}).setdefault(self._current_script, {})
        blank = next((name for name, rule in rules.items() if not str(rule.get('base', '')).strip() or str(rule.get('base', '')).strip() in {'main+0x0', '0', ''}), None)
        if blank:
            address, _baseline, _active, _current = candidates[0]
            offset = max(0, address - int(st.get('base', address)))
            rules[blank] = {'base': f'main+0x{offset:X}', 'offsets': [], 'type': 'i32', 'expect': {'nonzero': True}, 'enabled': False}
            save_settings(self.settings)
            self._log(f'[Mem自动采集] ② 回落候选 {len(candidates)} 个, 已填「{blank}」-> main+0x{offset:X} (默认禁用)')
        else:
            preview = ', '.join((hex(item[0]) for item in candidates[:10]))
            self._log(f'[Mem自动采集] ② 回落候选 {len(candidates)} 个, 无空白规则可填: {preview}')

    def _auto_scan(self):
        if not self._current_script:
            self._alert('提示', '请先选中一个驱动')
            return
        key = '自动监控'
        if self._popup_check(key):
            self._popup_windows[key].lift()
            return
        window = tk.Toplevel(self.root)
        window.title('自动监控')
        window.configure(bg='#1e1e2e')
        window.attributes('-topmost', True)
        self._popup_snap(window, key, 590, 310, lock_size=True)
        state = {'stop': False, 'done': False, 'ready': False, 'memory': self._ui_mem_get(), 'changed': [], 'change_hist': [], 'snap1': {}, 'results': []}

        def close():
            state['stop'] = True
            self._popup_windows.pop(key, None)
            self._popup_save_geo(window, key)
            window.destroy()
        self._popup_windows[key] = window
        window.protocol('WM_DELETE_WINDOW', close)
        window.bind('<Escape>', lambda _event: close())
        status = tk.StringVar(value='正在连接目标进程...')
        tk.Label(window, text='持续监控数据段变化，自动填充空白规则', bg='#1e1e2e', fg='#22d3ee', font=('Microsoft YaHei UI', 12, 'bold')).pack(pady=(20, 8))
        tk.Label(window, textvariable=status, bg='#1e1e2e', fg='#94a3b8').pack(pady=5)
        progress = ttk.Progressbar(window, mode='indeterminate', length=500)
        progress.pack(pady=8)
        button_bar = tk.Frame(window, bg='#1e1e2e')
        button_bar.pack(pady=12)
        snap1 = tk.Button(button_bar, text='① 记录弹码', command=lambda: self._auto_snap_phase1(state), bg='#38bdf8', fg='#0b1220', relief='flat', padx=16, pady=7, state='disabled')
        snap1.pack(side='left', padx=6)
        snap2 = tk.Button(button_bar, text='② 记录恢复', command=lambda: self._auto_snap_phase2(state), bg='#f97316', fg='white', relief='flat', padx=16, pady=7, state='disabled')
        snap2.pack(side='left', padx=6)
        tk.Button(button_bar, text='关闭监控', command=close, bg='#ef4444', fg='white', relief='flat', padx=16, pady=7).pack(side='left', padx=6)
        tk.Label(window, text='精准采集：弹出验证码后点①，关闭验证码后点②', bg='#1e1e2e', fg='#8b949e').pack(pady=4)
        if state['memory'] is None:
            status.set('未连接：请先绑定并启动游戏')
        else:
            progress.start(12)
            threading.Thread(target=self._mem_bg_loop, args=(state,), daemon=True).start()

        def update():
            if not window.winfo_exists():
                return
            if state.get('ready'):
                progress.stop()
                snap1.config(state='normal')
                snap2.config(state='normal')
                status.set(f"已连接 PID={state['memory'].pid} · 扫描 {state.get('scan_size', 0) // 1024}KB · 当前变化 {len(state.get('changed', []))}")
            elif state.get('conn_err'):
                progress.stop()
                status.set('扫描失败: ' + state['conn_err'])
            window.after(500, update)
        window.after(500, update)

    def _test_color_rule(self, name, key=None):
        if key and self._detect_busy.get(key):
            return
        if key:
            self._detect_busy[key] = True
        rules = self.settings.get('color_rules', {}).get(self._current_script, {})
        if name not in rules:
            self._log(f'[检测] {name}: 规则不存在')
            return
        points = rules[name]
        thresholds = self.settings.get('color_thresholds', {}).get(self._current_script, {})
        need_rate = thresholds.get(name, 100)
        need = max(1, int(len(points) * need_rate / 100))
        if getattr(self, '_detect_cam_until', 0) > time.time():
            if key:
                self._detect_busy.pop(key, None)
            return

        def run_check():
            error = None
            ok = False
            percent = 0
            hits = 0
            details = {}
            try:
                import numpy as np_local
                import cv2 as cv2_local
                if not hasattr(self, '_detect_cam') or self._detect_cam is None:
                    self._detect_cam = new_dxcam()
                camera = self._detect_cam
                with Screen._grab_lock:
                    try:
                        frame = camera.grab()
                    except Exception:
                        frame = None
                    if frame is None:
                        reset_dxcam()
                if frame is None:
                    self._detect_cam = None
                    self._detect_cam_until = time.time() + 5.0
                    error = '截图失败(相机失效, 已强制重建)'
                else:
                    if len(frame.shape) == 2:
                        frame = np_local.stack([frame, frame, frame], axis=-1)
                    frame = frame[:, :, :3]
                    bind_hwnd = self.settings.get('bind_hwnd', 0)
                    screen = Screen('')
                    if bind_hwnd and win32gui.IsWindow(bind_hwnd):
                        screen.hwnd = bind_hwnd
                    rect = screen.rect()
                    for index, config in enumerate(points):
                        x, y, width, height = cfg_region(config, rect)
                        x0 = max(0, x - rect[0])
                        y0 = max(0, y - rect[1])
                        x1 = min(frame.shape[1], x - rect[0] + width)
                        y1 = min(frame.shape[0], y - rect[1] + height)
                        image = frame[y0:y1, x0:x1] if x1 > x0 and y1 > y0 else frame[0:0]
                        if image.size == 0:
                            details[index + 1] = '?'
                            continue
                        raw_target = config.get('color')
                        if raw_target is None:
                            continue
                        target = np_local.array(raw_target, dtype=np_local.uint8)
                        tolerance = config.get('tol', DEFAULT_TOL)
                        lower = np_local.clip(target.astype(int) - tolerance, 0, 255).astype(np_local.uint8)
                        upper = np_local.clip(target.astype(int) + tolerance, 0, 255).astype(np_local.uint8)
                        matched = cv2_local.countNonZero(cv2_local.inRange(image[..., ::-1], lower, upper)) >= 3
                        if matched:
                            hits += 1
                            details[index + 1] = f"✓{config['color']}"
                        else:
                            details[index + 1] = '✗'
                    total = len(points)
                    percent = round(hits / total * 100) if total > 0 else 0
                    ok = hits >= need
            except Exception as exc:
                error = str(exc)
            self._safe_after(
                0,
                lambda: self._color_apply(
                    name, key, ok, percent, hits, details, error, need_rate, need
                ),
            )

        threading.Thread(target=run_check, daemon=True).start()

    def _color_apply(self, name, key, ok, pct, n_hit, details, err, need_rate, need):
        if key:
            self._detect_busy.pop(key, None)
        if err:
            self._log(f'[检测] {name}: {err}')
            return
        if key and not self._detect_running.get(key):
            return
        total = len(details)
        stats = self._detect_stats.setdefault(
            name, {'total': 0, 'hits': 0, 'results': []}
        )
        stats['total'] += 1
        if ok:
            stats['hits'] += 1
        detail_parts = [f'P{index}:{value}' for index, value in sorted(details.items())][-20:]
        stats['results'].append(
            f"{('✓' if ok else '✗')}{n_hit}/{total} [{' | '.join(detail_parts)}]"
        )
        if len(stats['results']) > 200:
            del stats['results'][:-200]
        self._detect_stats[name] = stats
        if key:
            last_ok = getattr(self, f'_last_{name}_ok', None)
            if ok != last_ok:
                setattr(self, f'_last_{name}_ok', ok)
                if ok:
                    self._log(f'[{name}] ✓ 已命中 ({pct}%)')
                else:
                    self._log(f'[{name}] ✗ 丢失')
            return
        status = '✓ 命中' if ok else '✗ 未命中'
        self._log(
            f'[检测] {name}: {status} · {n_hit}/{total}={pct}% '
            f'(需≥{need_rate}%即{need}个)'
        )

    def _styled_btn(self, parent, text, cmd=None, font=None, width=None, hover_bg=None):
        theme = self._t
        hover = hover_bg or theme['accent']
        button = tk.Button(parent, text=text, command=cmd, font=font or ('Microsoft YaHei UI', 9), width=width, bg=theme['card'], fg=theme['text'], activebackground=hover, activeforeground='white', relief='flat', cursor='hand2', bd=0, padx=8, pady=2, highlightthickness=1, highlightbackground=theme['tag'])
        button.bind('<Enter>', lambda _event, widget=button, color=hover: widget.configure(bg=color, highlightbackground=color))
        button.bind('<Leave>', lambda _event, widget=button: widget.configure(bg=theme['card'], highlightbackground=theme['tag']))
        button.bind('<ButtonPress-1>', lambda _event, widget=button: widget.configure(relief='sunken'))
        button.bind('<ButtonRelease-1>', lambda _event, widget=button: widget.configure(relief='flat'))
        return button

    def _bind_hover(self, widget, normal_bg, hover_bg):
        def enter(_event, target=widget, color=hover_bg):
            if getattr(self, '_bind_warn_on', False) and target is getattr(self, '_bind_btn', None):
                return
            target.configure(bg=color)

        def leave(_event, target=widget, color=normal_bg):
            if getattr(self, '_bind_warn_on', False) and target is getattr(self, '_bind_btn', None):
                return
            target.configure(bg=color)

        widget.bind('<Enter>', enter)
        widget.bind('<Leave>', leave)

    def _apply_theme(self):
        _refresh_pop()
        t = THEMES.get(_sys_theme(), THEMES['原始粉'])
        self.root.configure(bg=t['bg'])
        self._t = t
        return None

    def _build(self):
        theme = THEMES.get(_sys_theme(), THEMES['原始粉'])
        self._t = theme
        bg = theme['bg']
        card = theme['card']
        self.root.configure(bg=bg)

        def save_geometry(_event=None):
            if getattr(self, '_save_geo_after', None):
                try:
                    self.root.after_cancel(self._save_geo_after)
                except Exception:
                    pass

            def apply():
                if not self._closing and self.root.state() == 'normal':
                    self.settings['window_geo'] = self.root.geometry()
                    save_settings(self.settings)

            self._save_geo_after = self.root.after(500, apply)

        def toggle_lock():
            self._pos_locked = not self._pos_locked
            self.settings['pos_locked'] = self._pos_locked
            save_settings(self.settings)
            self.lock_label.configure(text='🔒' if self._pos_locked else '🔓')

        header = tk.Frame(self.root, bg=bg)
        header.pack(fill='x', padx=15, pady=(4, 6))
        user_text = '请激活' if not App._act_ok else (App._act_type or '已激活')
        self.activation_label = tk.Label(header, text=user_text, font=('Microsoft YaHei UI', 10, 'bold'), fg='#FFD700', bg=POP_CARD, cursor='hand2', padx=8, pady=3)
        self.activation_label.pack(side='left')
        self.activation_label.bind('<Button-1>', lambda _event: App._show_activate_dialog())
        self._bind_hover(self.activation_label, POP_CARD, POP_BTN)
        tk.Label(header, text='KEDriver · 驱动引擎', font=('Microsoft YaHei UI', 20, 'bold'), fg=theme['text'], bg=bg).place(relx=0.5, rely=0.5, anchor='center')

        links = tk.Frame(self.root, bg=bg)
        links.pack(fill='x', padx=15, pady=(2, 4))
        self.settings_label = tk.Label(links, text='设置', font=('Microsoft YaHei UI', 9), bg=POP_BTN, fg=POP_BTN_FG, cursor='hand2', padx=8, pady=2)
        self.settings_label.pack(side='right', padx=(0, 5))
        self.settings_label.bind('<Button-1>', lambda _event: self._open_settings())
        self._bind_hover(self.settings_label, POP_BTN, POP_HV)
        self.lock_label = tk.Label(links, text='🔒' if self._pos_locked else '🔓', font=('Microsoft YaHei UI', 9), bg=POP_CARD, fg=POP_BTN_FG, cursor='hand2', padx=6, pady=2)
        self.lock_label.pack(side='right', padx=(0, 3))
        self.lock_label.bind('<Button-1>', lambda _event: toggle_lock())

        status_row = tk.Frame(self.root, bg=card, relief='flat', bd=0)
        status_row.pack(fill='x', padx=15, pady=5)
        driver_box = tk.Frame(status_row, bg=POP_CARD)
        driver_box.pack(side='left', padx=(0, 6))
        self.driver_lbl = tk.Button(driver_box, text='', command=self._open_driver_helper, font=('Microsoft YaHei UI', 9, 'bold'), bg=POP_CARD, fg='#e6edf3', relief='flat', bd=0, cursor='hand2', activebackground=POP_HV, activeforeground='#ffffff', highlightthickness=0, padx=4, pady=0)
        self.driver_lbl.pack(padx=10, pady=3)
        self._bind_hover(self.driver_lbl, POP_CARD, POP_HV)
        self.status_text = tk.Label(status_row, text='就绪', font=('Microsoft YaHei UI', 12, 'bold'), bg=card, fg=theme['text'], cursor='hand2', relief='ridge', bd=1, padx=8, pady=2)
        self.status_text.pack(side='left')
        self.status_text.bind('<Button-1>', lambda _event: self._toggle())
        self.status_text.bind('<Double-1>', lambda _event: self._force_reset())
        self.status_label = self.status_text
        self.start_button = self.status_text

        self.hk_var = tk.StringVar(value=self.settings.get('hotkey_start', 'Home'))
        self.em_var = tk.StringVar(value=self.settings.get('emergency_key', 'End'))

        def hotkey_menu(parent, variable, setting_key):
            button = tk.Menubutton(parent, textvariable=variable, font=('Microsoft YaHei UI', 9), bg=POP_CARD, fg='#f2f2f2', relief='flat', bd=0, cursor='hand2', activebackground=POP_HV, activeforeground='#ffffff', highlightthickness=0, padx=6, pady=0)
            menu = tk.Menu(button, tearoff=False, bg=POP_CARD, fg='#f2f2f2')
            button.configure(menu=menu)
            for key_name in VK_MAP:
                def choose(value=key_name):
                    variable.set(value)
                    self.settings[setting_key] = value
                    save_settings(self.settings)
                menu.add_command(label=key_name, command=choose)
            return button

        emergency_button = hotkey_menu(status_row, self.em_var, 'emergency_key')
        emergency_button.pack(side='right', padx=(0, 8))
        tk.Label(status_row, text='强关:', font=('Microsoft YaHei UI', 9), bg=card, fg='#ff9800').pack(side='right', padx=(0, 2))
        start_hotkey_button = hotkey_menu(status_row, self.hk_var, 'hotkey_start')
        start_hotkey_button.pack(side='right', padx=(0, 10))
        tk.Label(status_row, text='启停:', font=('Microsoft YaHei UI', 9), bg=card, fg='#10b981').pack(side='right', padx=(0, 2))

        bind_row = tk.Frame(self.root, bg=card)
        bind_row.pack(fill='x', padx=15, pady=(0, 5))
        tk.Label(bind_row, text='目标窗口:', bg=card, fg='#888', font=('Microsoft YaHei UI', 9)).pack(side='left', padx=(5, 2))
        self._bind_title = tk.StringVar()
        self._update_bind_title(self.settings.get('bind_title', ''))
        self.bind_label = tk.Label(bind_row, textvariable=self._bind_title, width=24, anchor='w', font=('Microsoft YaHei UI', 9), bg=card, fg='#4CAF50')
        self.bind_label.pack(side='left', padx=2)
        self.bind_label.bind('<Enter>', self._bind_tip_show)
        self.bind_label.bind('<Leave>', self._bind_tip_hide)

        def clear_bind():
            self.settings.update(bind_hwnd=0, bind_title='', bind_pid=0, bind_exe='')
            save_settings(self.settings)
            self._update_bind_title('')
            self._drop_ui_mem()
            self._bind_warn_start()
            self._log('已清除窗口绑定')

        def pick_window():
            key = '绑定窗口'
            if self._popup_check(key):
                return
            window = tk.Toplevel(self.root)
            window.title(key)
            window.configure(bg=self.POPUP['bg'])
            window.transient(self.root)
            self._popup_snap(window, key, 520, 470)
            self._popup_register(window, key)
            top = tk.Frame(window, bg=self.POPUP['bg'])
            top.pack(fill='x', padx=12, pady=(12, 6))
            search_var = tk.StringVar()
            tk.Label(top, text='筛选:', bg=self.POPUP['bg'], fg=self.POPUP['text']).pack(side='left')
            search = tk.Entry(top, textvariable=search_var, bg=self.POPUP['entry_bg'], fg=self.POPUP['text'], insertbackground=self.POPUP['accent'], relief='flat')
            search.pack(side='left', fill='x', expand=True, padx=6)
            body = tk.Frame(window, bg=self.POPUP['bg'])
            body.pack(fill='both', expand=True, padx=12)
            scrollbar = tk.Scrollbar(body)
            scrollbar.pack(side='right', fill='y')
            window_list = tk.Listbox(body, bg=self.POPUP['entry_bg'], fg=self.POPUP['text'], selectbackground=self.POPUP['accent'], relief='flat', yscrollcommand=scrollbar.set)
            window_list.pack(fill='both', expand=True)
            scrollbar.configure(command=window_list.yview)
            rows = []

            def enumerate_windows():
                found = []
                def callback(hwnd, _extra):
                    try:
                        title = win32gui.GetWindowText(hwnd).strip()
                        if title and win32gui.IsWindowVisible(hwnd) and hwnd != self.root.winfo_id():
                            found.append((int(hwnd), title))
                    except Exception:
                        pass
                    return True
                win32gui.EnumWindows(callback, None)
                return sorted(found, key=lambda item: item[1].lower())

            def refresh(*_args):
                query = search_var.get().strip().lower()
                rows.clear()
                window_list.delete(0, 'end')
                for hwnd, title in enumerate_windows():
                    if query and query not in title.lower():
                        continue
                    rows.append((hwnd, title))
                    window_list.insert('end', title)

            def save_selection(_event=None):
                selection = window_list.curselection()
                if not selection:
                    return
                hwnd, title = rows[selection[0]]
                self.settings['bind_hwnd'] = hwnd
                self.settings['bind_title'] = title
                try:
                    _, pid = win32gui.GetWindowThreadProcessId(hwnd)
                    self.settings['bind_pid'] = int(pid)
                except Exception:
                    self.settings['bind_pid'] = 0
                save_settings(self.settings)
                self._update_bind_title(title)
                self._drop_ui_mem()
                self._bind_warn_stop()
                self._show_bind_highlight(hwnd)
                self._log(f'已绑定窗口: {title}')
                window.destroy()

            search_var.trace_add('write', refresh)
            window_list.bind('<Double-1>', save_selection)
            buttons = tk.Frame(window, bg=self.POPUP['bg'])
            buttons.pack(fill='x', padx=12, pady=10)
            tk.Button(buttons, text='刷新', command=refresh, bg=POP_BTN, fg=POP_BTN_FG, relief='flat', padx=12, pady=4).pack(side='left')
            tk.Button(buttons, text='绑定所选', command=save_selection, bg=self.POPUP['accent'], fg='white', relief='flat', padx=14, pady=4).pack(side='right')
            tk.Button(buttons, text='绑定当前前台', command=lambda: (window.destroy(), self._bind_foreground()), bg=POP_BTN, fg=POP_BTN_FG, relief='flat', padx=14, pady=4).pack(side='right', padx=6)
            refresh()
            search.focus_set()

        self._bind_btn = tk.Button(bind_row, text='绑定窗口', command=pick_window, font=('Microsoft YaHei UI', 8, 'bold'), bg=POP_BTN, fg=POP_BTN_FG, relief='flat', padx=6, pady=1)
        self._bind_btn.pack(side='right', padx=2)
        self._bind_hover(self._bind_btn, POP_BTN, POP_HV)
        clear_button = tk.Button(bind_row, text='清除', command=clear_bind, font=('Microsoft YaHei UI', 8, 'bold'), bg=POP_BTN, fg=POP_BTN_FG, relief='flat', padx=4, pady=1)
        clear_button.pack(side='right', padx=2)
        self._bind_hover(clear_button, POP_BTN, POP_HV)

        list_card = tk.LabelFrame(self.root, text='进程列表', bg=bg, fg=theme['text'], font=('Microsoft YaHei UI', 10), padx=0, pady=0)
        list_card.pack(fill='x', padx=15, pady=(10, 5))
        tree_frame = tk.Frame(list_card, bg=bg)
        tree_frame.pack(fill='x', padx=5, pady=5)
        style = ttk.Style(self.root)
        try:
            style.theme_use('clam')
        except Exception:
            pass
        style.configure('Scripts.Treeview', background=theme.get('list_bg', '#262626'), fieldbackground=theme.get('list_bg', '#262626'), foreground=theme.get('list_fg', '#d6d2ca'), bordercolor='#11161f', rowheight=26, font=('Microsoft YaHei UI', 10, 'bold'))
        style.map('Scripts.Treeview', background=[('selected', theme.get('list_sel', '#3a3a3a'))], foreground=[('selected', theme.get('list_sel_fg', '#ffffff'))])
        style.configure('Scripts.Treeview.Heading', background=theme.get('head_bg', '#262626'), foreground=theme.get('head_fg', '#e6edf3'), relief='flat', padding=(6, 4), font=('Microsoft YaHei UI', 10))
        style.map('Scripts.Treeview.Heading', background=[('active', theme.get('head_hover', '#353535'))])
        self.script_list = ttk.Treeview(tree_frame, columns=('tag', 'name', 'desc'), show='headings', height=5, selectmode='browse', style='Scripts.Treeview')
        for column, text_value, width in (('tag', '类型', 50), ('name', '名称', 110), ('desc', '功能', 200)):
            self.script_list.heading(column, text=text_value, anchor='w')
            self.script_list.column(column, width=width, stretch=column == 'desc')
        self.script_list.pack(side='left', fill='x', expand=True)
        tree_scroll = tk.Scrollbar(tree_frame, command=self.script_list.yview, width=10)
        tree_scroll.place(in_=self.script_list, relx=1.0, x=2, rely=0, relheight=1.0, anchor='ne')
        self.script_list.configure(yscrollcommand=tree_scroll.set)
        self.script_list.bind('<<TreeviewSelect>>', self._on_script_select)
        button_row = tk.Frame(list_card, bg=bg)
        button_row.pack(pady=5)
        self._styled_btn(button_row, '进程管理', self._game_manager, width=8).pack(side='right', padx=2)
        for text_value, command in (
            ('新建', self._new_script),
            ('导入', self._import_script),
            ('导出', self._export_script),
            ('编辑', self._edit_script),
            ('移除', self._delete_script),
            ('刷新', self._refresh_list),
        ):
            self._styled_btn(button_row, text_value, command, width=6).pack(side='left', padx=2)

        rule_card = tk.LabelFrame(self.root, text='规则信息', bg=bg, fg=theme['text'], font=('Microsoft YaHei UI', 10), padx=0, pady=0)
        rule_card.pack(fill='x', padx=15, pady=5)
        rule_buttons = tk.Frame(rule_card, bg=bg)
        rule_buttons.pack(pady=(4, 6))

        def import_rules():
            if not self._current_script:
                self._alert('提示', '请先选择驱动')
                return
            candidates = [item for item in list_scripts() if item['file'] != self._current_script]
            if not candidates:
                self._alert('导入规则', '没有其他可导入规则的驱动')
                return
            source_name = self._ask_string(self.root, '导入规则', '输入来源驱动文件名', candidates[0]['file'])
            if not source_name:
                return
            source = next((item['file'] for item in candidates if item['file'] == source_name or item.get('name') == source_name), None)
            if not source:
                self._alert('导入规则', '未找到来源驱动')
                return
            copied = 0
            for setting_key in ('color_rules', 'color_thresholds', 'color_rules_enabled', 'img_rules_regions', 'img_thresholds', 'memory_rules'):
                group = self.settings.setdefault(setting_key, {})
                if source in group:
                    group[self._current_script] = copy.deepcopy(group[source])
                    copied += 1
            save_settings(self.settings)
            self._log(f'已从 {source} 导入 {copied} 类规则')

        rule_button = tk.Button(rule_buttons, text='规则', command=self._open_color_lib, font=('Microsoft YaHei UI', 9, 'bold'), bg=POP_BTN, fg=POP_BTN_FG, relief='flat', cursor='hand2', activebackground=POP_HV, activeforeground='white', padx=12, pady=2)
        rule_button.pack(side='left', padx=2)
        self._bind_hover(rule_button, POP_BTN, POP_HV)
        import_button = tk.Button(rule_buttons, text='导入规则', command=import_rules, font=('Microsoft YaHei UI', 8), bg=POP_BTN, fg=POP_BTN_FG, relief='flat', cursor='hand2', padx=6, pady=2)
        import_button.pack(side='left', padx=2)
        self._bind_hover(import_button, POP_BTN, POP_HV)
        mem_button = tk.Button(rule_buttons, text='AI-Mem', command=self._open_mem_rules, font=('Microsoft YaHei UI', 9, 'bold'), bg=POP_BTN, fg=POP_BTN_FG, relief='flat', cursor='hand2', activebackground=POP_HV, activeforeground='white', padx=8, pady=2)
        mem_button.pack(side='left', padx=2)
        self._bind_hover(mem_button, POP_BTN, POP_HV)

        def open_sample_box():
            try:
                os.makedirs(SHOT_DIR, exist_ok=True)
                os.startfile(SHOT_DIR)
            except Exception as exc:
                self._log(f'打开样本箱失败: {exc}')

        sample_button = tk.Button(rule_buttons, text='样本箱', command=open_sample_box, font=('Microsoft YaHei UI', 8), bg=POP_BTN, fg=POP_BTN_FG, relief='flat', cursor='hand2', padx=6, pady=2)
        sample_button.pack(side='left', padx=2)
        self._bind_hover(sample_button, POP_BTN, POP_HV)
        status_outer = tk.Frame(rule_card, bg=bg)
        status_outer.pack(fill='x', pady=(0, 2))
        status_bar = tk.Frame(status_outer, bg=bg)
        status_bar.pack(fill='x', padx=8, pady=3)
        status_inner = tk.Frame(status_bar, bg=bg)
        status_inner.pack()
        self._ai_lbl = tk.Label(status_inner, text='🤖 验证码: 等待', font=('Microsoft YaHei UI', 9, 'bold'), fg=POP_SUB, bg=bg, anchor='w', justify='left')
        self._ai_lbl.pack(side='left', padx=(0, 14))
        self._ai_mem_lbl = tk.Label(status_inner, text='Mem: 未连接', font=('Microsoft YaHei UI', 9, 'bold'), fg=POP_SUB, bg=bg, anchor='w', justify='left')
        self._ai_mem_lbl.pack(side='left')

        wizard_frame = tk.Frame(self.root, bg=bg)
        wizard_frame.pack(pady=8)
        wizard = tk.Button(wizard_frame, text='规则配置向导', command=self._script_wizard, font=('Microsoft YaHei UI', 16, 'bold'), bg=POP_BTN, fg=POP_BTN_FG, activebackground=POP_HV, activeforeground='white', relief='flat', cursor='hand2', width=20, height=2)
        wizard.pack()
        self._bind_hover(wizard, POP_BTN, POP_HV)
        tk.Label(wizard_frame, text='选择LUA文件开始配置', bg=bg, fg=theme['sub'], font=('Microsoft YaHei UI', 9)).pack(pady=(2, 0))

        capture_row = tk.Frame(self.root, bg=bg)
        capture_row.pack(pady=(5, 0))
        for text_value, mode, color in (('🎨 取色', 'point', '#E91E63'), ('📝 取字', 'ocr', '#2196F3'), ('🖼 取图', 'img', '#4CAF50')):
            self._styled_btn(capture_row, text_value, lambda value=mode: self._quick_capture(value), width=8, hover_bg=color).pack(side='left', padx=2)

        log_frame = tk.Frame(self.root, bg=theme['log_bg'])
        log_frame.pack(fill='both', expand=True, padx=15, pady=8)
        log_header = tk.Frame(log_frame, bg=theme['log_bg'])
        log_header.pack(fill='x')
        copy_button = tk.Button(log_header, text='复制', command=lambda: self._copy_log_text(), font=('Microsoft YaHei UI', 10), bg=POP_BTN, fg=POP_BTN_FG, relief='flat', cursor='hand2', padx=6, pady=1)
        copy_button.pack(side='left')
        clear_button = tk.Button(log_header, text='清屏', command=lambda: self._clear_log_text(), font=('Microsoft YaHei UI', 10), bg=POP_BTN, fg=POP_BTN_FG, relief='flat', cursor='hand2', padx=4, pady=1)
        clear_button.pack(side='right')
        self._bind_hover(copy_button, POP_BTN, POP_HV)
        self._bind_hover(clear_button, POP_BTN, POP_HV)
        tk.Label(log_header, text='软件仅供学习交流和技术研究使用', bg=theme['log_bg'], fg='#f44336', font=('Microsoft YaHei UI', 10)).place(relx=0.5, rely=0.5, anchor='center')
        self.log_area = tk.Text(log_frame, font=('Consolas', 10), bg=theme['log_bg'], fg=theme['log_fg'], insertbackground=theme['log_fg'], wrap='word', relief='flat', borderwidth=0, highlightthickness=0, state='disabled')
        try:
            import tkinter.font as tk_font
            hanging_indent = int(
                tk_font.Font(family='Consolas', size=10).measure('00:00:00 ')
            ) + 2
        except Exception:
            hanging_indent = 60
        self.log_area.tag_config('hang', lmargin1=0, lmargin2=hanging_indent)
        self.log_area.tag_config('pass', foreground='#10b981')
        self.log_area.tag_config('fail', foreground='#ef4444')
        self.log_area.tag_config('warn', foreground='#f08080')
        self.log_area.tag_config('fight', foreground='#f97316')
        self.log_area.tag_config('loot', foreground='#3b82f6')
        self.log_area.tag_config('dodge', foreground='#06b6d4')
        self.log_area.tag_config('captcha_crop', foreground='#00bfff')
        self.log_area.tag_config('captcha_input', foreground='#00e676')
        self.log_area.tag_config('captcha_ok', foreground='#ff6d00')
        log_scroll = tk.Scrollbar(
            self.root,
            command=self.log_area.yview,
            borderwidth=0,
            troughcolor=theme['log_bg'],
            width=10,
        )
        self.log_area.configure(yscrollcommand=log_scroll.set)
        self.log_area.pack(side='left', fill='both', expand=True)
        self.log_area.bind('<MouseWheel>', lambda event: self.log_area.yview_scroll(int(-event.delta / 120), 'units'))
        self.log_box = self.log_area
        self._wiz_names = ['色检1']
        self._wiz_idx = [0]
        self._wiz_total = 1
        self._cap_mode = ''
        self.root.bind('<Configure>', save_geometry, add='+')
        if self.settings.get('bind_title'):
            self._bind_warn_stop()
        else:
            self._bind_warn_start()
        self._refresh_driver_ui()

    def _copy_log_text(self):
        try:
            text = self.log_area.get('1.0', 'end-1c')
            self.root.clipboard_clear()
            self.root.clipboard_append(text)
            self._log('日志已复制')
        except Exception as exc:
            self._log(f'复制日志失败: {exc}')

    def _clear_log_text(self):
        with self._log_lock:
            self._log_lines.clear()
        try:
            self.log_area.config(state='normal')
            self.log_area.delete('1.0', 'end')
            self.log_area.see('end')
            self.log_area.config(state='disabled')
        except Exception:
            pass

    def _wiz_show_step(self, i):
        names = getattr(self, '_wiz_names', [])
        if i >= len(names):
            self._log('取色向导已完成')
            self._popup_windows.pop('取色向导', None)
            return
        self._wizard_step = i
        key = '取色向导'
        old = self._popup_windows.get(key)
        if old and old.winfo_exists():
            old.destroy()
            self._popup_windows.pop(key, None)
        window = tk.Toplevel(self.root)
        window.title(f'取色向导 {i + 1}/{len(names)}')
        window.configure(bg=self.POPUP['bg'])
        window.attributes('-topmost', True)
        window.transient(self.root)
        self._popup_snap(window, key, 430, 235, lock_size=True)
        self._popup_register(window, key)
        tk.Label(window, text=f'步骤 {i + 1} / {len(names)}', bg=self.POPUP['bg'], fg=self.POPUP['sub']).pack(pady=(18, 4))
        tk.Label(window, text=f'「{names[i]}」', bg=self.POPUP['bg'], fg=self.POPUP['accent'], font=('Microsoft YaHei UI', 15, 'bold')).pack(pady=3)
        tk.Label(window, text='拖拽框选目标区域后自动保存', bg=self.POPUP['bg'], fg=self.POPUP['text']).pack(pady=5)
        mode_names = {'color': '🎨 取色', 'ocr': '📝 取字', 'img': '🖼 抠图'}
        mode = tk.StringVar(value=getattr(self, '_wiz_rule_type', 'color'))

        def cycle_mode():
            values = ['color', 'ocr', 'img']
            mode.set(values[(values.index(mode.get()) + 1) % len(values)])
            self._wiz_rule_type = mode.get()
            mode_button.config(text=mode_names[mode.get()])

        def capture():
            self._wiz_rule_type = mode.get()
            self._cap_mode = mode.get()
            window.withdraw()
            self._start_region_selector()
        buttons = tk.Frame(window, bg=self.POPUP['bg'])
        buttons.pack(pady=12)
        mode_button = tk.Button(buttons, text=mode_names[mode.get()], command=cycle_mode, bg='#6b7280', fg='white', relief='flat', padx=14, pady=6)
        mode_button.pack(side='left', padx=5)
        tk.Button(buttons, text='开始框选', command=capture, bg=self.POPUP['accent'], fg='white', relief='flat', padx=18, pady=6).pack(side='left', padx=5)
        tk.Button(buttons, text='取消', command=lambda: window.destroy(), bg='#ef4444', fg='white', relief='flat', padx=14, pady=6).pack(side='left', padx=5)
        window.bind('<Escape>', lambda _event: window.destroy())

    def _wiz_next(self):
        self._wizard_step = getattr(self, '_wizard_step', 0) + 1
        self._wiz_show_step(self._wizard_step)

    def _insert_code(self, code):
        if not self._current_script:
            return
        path = os.path.join(SCRIPTS_DIR, self._current_script)
        source = lua_read_text(path)
        lua_write_text(path, source + '\n' + code + '\n')

    def _auto_save(self, rx, ry, rw, rh, cap, name=None):
        if name is None:
            names = getattr(self, '_wiz_names', [])
            index = getattr(self, '_wizard_step', 0)
            name = names[index] if index < len(names) else f'规则{int(time.time())}'
        if not name or not self._current_script or cap is None or (cap.size == 0):
            return None
        height, width = cap.shape[:2]
        center_x, center_y = (width // 2, height // 2)
        x0, x1 = (max(0, center_x - 5), min(width, center_x + 5))
        y0, y1 = (max(0, center_y - 5), min(height, center_y + 5))
        color_rules = []
        for py in range(y0, y1):
            for px in range(x0, x1):
                red, green, blue = (int(value) for value in cap[py, px, :3])
                color_rules.append(make_color_rule(round(rx + px * rw / max(width, 1), 2), round(ry + py * rh / max(height, 1), 2), [red, green, blue], w_pct=rw, h_pct=rh))
        rules = self.settings.setdefault('color_rules', {}).setdefault(self._current_script, {})
        rules[name] = color_rules
        threshold = self.settings.setdefault('color_thresholds', {}).setdefault(self._current_script, {}).get(name, 100)
        self.settings.setdefault('color_thresholds', {}).setdefault(self._current_script, {})[name] = threshold
        save_settings(self.settings)
        try:
            color_dir = os.path.join(SCRIPT_DIR, '色库')
            os.makedirs(color_dir, exist_ok=True)
            Image.fromarray(cap).save(os.path.join(color_dir, f"{name}_{time.strftime('%m%d_%H%M%S')}.png"))
        except Exception:
            pass
        minimum_hits = max(1, int(len(color_rules) * threshold / 100))
        self._log(f'  -> {name}: {len(color_rules)}色点 · 匹配率{threshold}%（需{minimum_hits}个命中）')
        return name

    def _quick_color_info(self, cap_img):
        if cap_img is None or cap_img.size == 0:
            return None
        height, width = cap_img.shape[:2]
        center_x, center_y = (width // 2, height // 2)
        sample = cap_img[max(0, center_y - 5):min(height, center_y + 5), max(0, center_x - 5):min(width, center_x + 5), :3].reshape(-1, 3)
        groups = []
        for color in sample:
            rgb = tuple((int(value) for value in color))
            for group in groups:
                if all((abs(rgb[index] - group[0][index]) < 15 for index in range(3))):
                    group[1] += 1
                    break
            else:
                groups.append([rgb, 1])
        groups.sort(key=lambda item: item[1], reverse=True)
        summary = ' '.join((f'RGB{group[0]}x{group[1]}' for group in groups[:4]))
        self._log(f'[取色] 框内{len(sample)}色点 · 高频色: {summary}')
        return groups[0][0] if groups else None

    def _test_on_region(self, name, cap_img, rv, gv, bv):
        if cap_img is None:
            return False
        target = np.array([bv, gv, rv], dtype=np.uint8)
        mask = cv2.inRange(cap_img, np.clip(target.astype(int) - 30, 0, 255).astype(np.uint8), np.clip(target.astype(int) + 30, 0, 255).astype(np.uint8))
        return cv2.countNonZero(mask) >= 3

    def _flash_region(self, x, y, w, h, color, duration=800):
        overlay = tk.Toplevel(self.root)
        overlay.overrideredirect(True)
        overlay.attributes('-topmost', True)
        overlay.geometry(f'{w}x{h}+{x}+{y}')
        overlay.configure(bg=color)
        try:
            overlay.attributes('-alpha', 0.35)
        except Exception:
            pass
        overlay.after(duration, overlay.destroy)

    def _check_autostart(self):
        try:
            startup = os.path.join(
                os.environ['APPDATA'],
                'Microsoft',
                'Windows',
                'Start Menu',
                'Programs',
                'Startup',
            )
            old_link = os.path.join(startup, 'KE外设.lnk')
            if os.path.exists(old_link):
                try:
                    os.remove(old_link)
                except Exception:
                    pass
            return os.path.exists(os.path.join(startup, 'K3M2.lnk'))
        except Exception:
            return False

    def _open_settings(self):
        if self._popup_check('设置'):
            return
        bg = self._t['bg']
        card = self._t['card']
        accent = self._t['accent']
        text_color = self._t['text']
        sub_color = self._t['sub']
        window = tk.Toplevel(self.root)
        window.title('KE Driver 设置')
        window.attributes('-topmost', True)
        window.transient(self.root)
        window.resizable(False, False)
        window.configure(bg=self.POPUP['bg'])
        self._popup_register(window, '设置')
        self._popup_snap(window, '设置', 420, 280)

        float_var = tk.BooleanVar(value=self.settings.get('float_show', True))
        voice_var = tk.BooleanVar(value=self.settings.get('voice', True))
        autostart_var = tk.BooleanVar(value=self._check_autostart())
        privacy_var = tk.BooleanVar(value=self.settings.get('privacy', False))
        clean_var = tk.StringVar(value=str(self.settings.get('clean_days', '30')))

        frame = tk.Frame(window, bg=self.POPUP['bg'])
        frame.pack(expand=True)
        check_style = {
            'bg': self.POPUP['bg'],
            'activebackground': self.POPUP['bg'],
            'selectcolor': self.POPUP['card'],
            'fg': self.POPUP['text'],
            'font': ('Microsoft YaHei UI', 10),
        }
        tk.Checkbutton(
            frame, text='悬浮窗', variable=float_var, **check_style
        ).pack(anchor='w', pady=2)
        try:
            float_size = int(self.settings.get('float_size', 17))
        except (TypeError, ValueError):
            float_size = 17
        fs_var = tk.IntVar(value=float_size)
        size_row = tk.Frame(frame, bg=self.POPUP['bg'])
        size_row.pack(anchor='w', pady=2)
        tk.Label(
            size_row,
            text='  悬浮窗字号',
            font=('Microsoft YaHei UI', 10),
            bg=self.POPUP['bg'],
            fg=self.POPUP['text'],
        ).pack(side='left', padx=(0, 6))
        ttk.Combobox(
            size_row,
            textvariable=fs_var,
            values=[7, 9, 11, 14, 17, 20],
            state='readonly',
            width=5,
            font=('Microsoft YaHei UI', 10),
        ).pack(side='left')
        tk.Label(
            frame,
            text='  点击启停 · 右键关闭 · 拖拽移动',
            bg=self.POPUP['bg'],
            fg=self.POPUP['sub'],
            font=('Microsoft YaHei UI', 8),
        ).pack(anchor='w')
        tk.Checkbutton(
            frame,
            text='语音提示',
            variable=voice_var,
            command=lambda: (
                self.settings.update({'voice': voice_var.get()}),
                save_settings(self.settings),
            ),
            **check_style,
        ).pack(anchor='w', pady=2)
        tk.Checkbutton(
            frame, text='开机自启', variable=autostart_var, **check_style
        ).pack(anchor='w', pady=2)
        tk.Checkbutton(
            frame, text='隐私遮盖', variable=privacy_var, **check_style
        ).pack(anchor='w', pady=2)
        clean_row = tk.Frame(frame, bg=self.POPUP['bg'])
        clean_row.pack(anchor='w', pady=2)
        tk.Label(
            clean_row,
            text='清理天数',
            font=('Microsoft YaHei UI', 10),
            bg=self.POPUP['bg'],
            fg=self.POPUP['text'],
        ).pack(side='left', padx=(0, 6))
        ttk.Combobox(
            clean_row,
            textvariable=clean_var,
            values=['1', '3', '7', '14', '30', '0'],
            state='readonly',
            width=5,
            font=('Microsoft YaHei UI', 10),
        ).pack(side='left')

        def apply(*_args):
            try:
                self.settings['float_show'] = float_var.get()
                self.settings['voice'] = voice_var.get()
                self.settings['privacy'] = privacy_var.get()
                days = int(clean_var.get())
                if days > 0:
                    self.settings['clean_days'] = str(days)
                size = int(fs_var.get())
                self.settings['float_size'] = size
                if hasattr(self, '_float_lbl') and self._float_lbl:
                    self._float_lbl.config(
                        font=('Microsoft YaHei UI', size, 'bold')
                    )
                if (
                    hasattr(self, '_fw')
                    and self._fw
                    and self._fw.winfo_exists()
                ):
                    self._fw.geometry(
                        f'{size * 10 + 30}x{size + 14}+'
                        f'{self._fw.winfo_x()}+{self._fw.winfo_y()}'
                    )
                startup = os.path.join(
                    os.environ['APPDATA'],
                    'Microsoft',
                    'Windows',
                    'Start Menu',
                    'Programs',
                    'Startup',
                    'K3M2.lnk',
                )
                if autostart_var.get():
                    import subprocess
                    escaped = startup.replace("'", "''")
                    command = (
                        "$w=(New-Object -ComObject WScript.Shell)."
                        f"CreateShortcut('{escaped}');"
                        "$w.TargetPath='schtasks.exe';"
                        "$w.Arguments='/run /tn \"AutoHelper\"';$w.Save()"
                    )
                    subprocess.run(
                        ['powershell', '-Command', command],
                        check=False,
                        creationflags=subprocess.CREATE_NO_WINDOW,
                    )
                elif os.path.exists(startup):
                    os.remove(startup)
                save_settings(self.settings)
                if privacy_var.get():
                    self.root.after(600, self._show_privacy_bar)
                else:
                    self._hide_privacy_bar()
                if (
                    hasattr(self, '_fw')
                    and self._fw
                    and self._fw.winfo_exists()
                ):
                    if float_var.get():
                        self._fw.deiconify()
                    else:
                        self._fw.withdraw()
            except Exception:
                pass

        for variable in (
            float_var,
            voice_var,
            autostart_var,
            privacy_var,
            clean_var,
            fs_var,
        ):
            variable.trace_add('write', apply)

    def _show_privacy_bar(self):
        if not self.settings.get('privacy', False):
            return None
        current = getattr(self, '_privacy_win', None)
        if current and current.winfo_exists():
            current.lift()
            return current
        geometry = self.settings.get('cover_geo', '200x50+100+100')
        text = self.settings.get('cover_text', '抖音丶KE')
        window = tk.Toplevel(self.root)
        window.overrideredirect(True)
        window.attributes('-topmost', True)
        window.geometry(geometry)
        window.configure(bg='#000000')
        label = tk.Label(window, text=text, bg='#000000', fg='#e94560', font=('Microsoft YaHei UI', 15, 'bold'))
        label.pack(fill='both', expand=True)
        self._privacy_win = self._privacy_bar = window
        drag = {'x': 0, 'y': 0}
        resize = {'x': 0, 'y': 0, 'w': 0, 'h': 0}

        def edit_text(_event=None):
            value = self._ask_string(self.root, '隐私遮盖', '遮盖文字', label.cget('text'))
            if value:
                label.config(text=value)
                self.settings['cover_text'] = value
                save_settings(self.settings)

        def start(event):
            drag['x'], drag['y'] = (event.x_root - window.winfo_x(), event.y_root - window.winfo_y())

        def move(event):
            window.geometry(f"+{event.x_root - drag['x']}+{event.y_root - drag['y']}")

        def end(_event):
            self.settings['cover_geo'] = window.geometry()
            save_settings(self.settings)
        label.bind('<Double-Button-1>', edit_text)
        label.bind('<ButtonPress-1>', start)
        label.bind('<B1-Motion>', move)
        label.bind('<ButtonRelease-1>', end)
        grip = tk.Label(window, text='◢', bg='#000000', fg='#e94560', cursor='bottom_right_corner')
        grip.place(relx=1.0, rely=1.0, anchor='se')

        def resize_start(event):
            resize.update(x=event.x_root, y=event.y_root, w=window.winfo_width(), h=window.winfo_height())

        def resize_move(event):
            width = max(80, resize['w'] + event.x_root - resize['x'])
            height = max(30, resize['h'] + event.y_root - resize['y'])
            window.geometry(f'{width}x{height}')
            label.config(font=('Microsoft YaHei UI', max(8, min(40, height // 3)), 'bold'))
        grip.bind('<ButtonPress-1>', resize_start)
        grip.bind('<B1-Motion>', resize_move)
        grip.bind('<ButtonRelease-1>', end)
        return window

    def _hide_privacy_bar(self):
        if self._privacy_bar:
            try:
                self._privacy_bar.destroy()
            except Exception:
                pass
        self._privacy_bar = None
        self._privacy_win = None

    def _script_wizard(self, reset=False):
        if not self._current_script:
            self._alert('提示', '请先选择驱动')
            return
        names = []
        try:
            source = lua_read_text(os.path.join(SCRIPTS_DIR, self._current_script))
            source = re.sub('--.*', '', source)
            for match in re.finditer('(?:test_color|find_color|color_rule)\\s*\\(\\s*[\'\\"]([^\'\\"]+)', source):
                name = match.group(1).strip()
                if name and name not in names:
                    names.append(name)
        except Exception:
            pass
        for name in self.settings.get('color_rules', {}).get(self._current_script, {}):
            if name not in names:
                names.append(name)
        if reset or not names:
            value = self._ask_string(self.root, '新建规则', '输入规则名（多个用逗号分隔）：')
            if not value:
                self._log('取消配置')
                return
            names = [item.strip() for item in value.split(',') if item.strip()]
        if not names:
            self._log('规则配置向导启动失败')
            return
        self._wiz_names = names
        self._wiz_idx = 0
        self._wiz_total = len(names)
        self._wiz_rule_type = 'color'
        self._wiz_show_step(0)

    def _alert(self, title, msg):
        try:
            messagebox.showinfo(title, msg, parent=self.root)
        except Exception:
            print(f'{title}: {msg}')

    def _start_hotkey_thread(self):

        def poll():
            last_start = False
            last_emergency = False
            while not self._closing:
                try:
                    start_key = VK_MAP.get(self.settings.get('hotkey_start', 'Home'), 36)
                    emergency_key = VK_MAP.get(self.settings.get('emergency_key', 'End'), 35)
                    start_down = bool(win32api.GetAsyncKeyState(start_key) & 32768)
                    emergency_down = bool(win32api.GetAsyncKeyState(emergency_key) & 32768)
                    if start_down and (not last_start):
                        ke_sentinel.on_hotkey_press()
                        self._after_queue.put((self._toggle, ()))
                    if not start_down and last_start:
                        ke_sentinel.on_hotkey_toggle()
                    if emergency_down and (not last_emergency):
                        self._after_queue.put((self._stop, ()))
                    last_start, last_emergency = (start_down, emergency_down)
                except Exception:
                    pass
                time.sleep(0.03)
        threading.Thread(target=poll, daemon=True).start()

    def _toggle(self):
        if self._running or self._starting:
            self._stop()
        else:
            self._start()

    def _toggle_driver(self):
        modes = ['ttinput']
        names = {'ttinput': 'KE Driver', 'Interception': '兼容模式'}
        try:
            index = modes.index(self._driver_mode)
        except ValueError:
            index = 0
        self._driver_mode = modes[(index + 1) % len(modes)]
        self.settings['input_mode'] = self._driver_mode
        save_settings(self.settings)
        self._refresh_driver_ui()
        self._log(f'驱动切换 →{names.get(self._driver_mode, self._driver_mode)}')

    def _refresh_driver_ui(self):
        if not hasattr(self, 'driver_lbl'):
            return None
        colors = {'viiper': '#2dd4bf', 'ttinput': '#10b981', 'fakerinput': '#e879f9'}
        labels = {'viiper': 'VIIPER', 'ttinput': 'KE Driver', 'fakerinput': 'FakerInput'}
        mode = getattr(self, '_driver_mode', 'viiper')
        if self._driver_installed(mode):
            self.driver_lbl.config(text=labels.get(mode, mode), fg=colors.get(mode, '#888'))
            return None
        self.driver_lbl.config(text='驱动未安装', fg='#f85149')
        return None

    def _check_driver(self):
        """Install the bundled TTInput device when its service/device is absent."""
        import subprocess
        driver_dir = getattr(sys, '_MEIPASS', None) or SCRIPT_DIR
        if driver_dir != SCRIPT_DIR and (not os.path.exists(os.path.join(driver_dir, 'devcon.exe'))):
            driver_dir = SCRIPT_DIR
        try:
            result = subprocess.run(['sc.exe', 'query', 'ttinputhid'], capture_output=True, text=True, encoding='gbk', errors='replace', timeout=5, creationflags=getattr(subprocess, 'CREATE_NO_WINDOW', 0))
            service_running = 'RUNNING' in (result.stdout or '')
            service_stopped = 'STOPPED' in (result.stdout or '')
        except Exception as exc:
            service_running = service_stopped = False
            self._after_queue.put((self._log, (f'[驱动] 服务检查异常: {exc}',)))
        if service_running:
            devcon = os.path.join(driver_dir, 'devcon.exe')
            if not os.path.exists(devcon):
                self._after_queue.put((self._log, ('[驱动] devcon.exe 缺失',)))
                return
            try:
                device = subprocess.run([devcon, 'findall', 'ROOT\\ttinput*'], capture_output=True, text=True, encoding='gbk', errors='replace', timeout=10, creationflags=getattr(subprocess, 'CREATE_NO_WINDOW', 0))
                if 'ROOT' in (device.stdout or ''):
                    return
                self._after_queue.put((self._log, ('[驱动] 服务在但设备缺失, 尝试重装...',)))
            except Exception as exc:
                self._after_queue.put((self._log, (f'[驱动] 设备检查异常: {exc}',)))
                return
        inf = os.path.join(driver_dir, 'ttinput.inf')
        sys_file = os.path.join(driver_dir, 'ttinput.sys')
        devcon = os.path.join(driver_dir, 'devcon.exe')
        if not all((os.path.exists(path) for path in (inf, sys_file, devcon))):
            self._after_queue.put((self._log, ('[驱动] 驱动文件不齐(inf/sys/devcon), 跳过自动安装',)))
            return
        install_bat = os.path.join(SCRIPT_DIR, '_install_driver.bat')
        script = f'@echo off\r\nchcp 65001 >nul\r\nset "DV={driver_dir}"\r\necho 正在准备安装环境...\r\n"%DV%\\devcon.exe" remove ROOT\\ttinput* >nul 2>&1\r\nsc stop ttinputhid >nul 2>&1\r\nsc delete ttinputhid >nul 2>&1\r\ntimeout /t 3 /nobreak >nul\r\necho 正在安装软件驱动, 请稍候...\r\n"%DV%\\devcon.exe" install "%DV%\\ttinput.inf" ROOT\\ttinput > "%~dp0安装记录.txt" 2>&1\r\nif %errorlevel% equ 0 (echo [OK] 完成 & timeout /t 2 >nul & del "%~dp0安装记录.txt" >nul 2>&1 & del "%~f0" & exit /b 0)\r\necho 首次未成功, 自动重试...\r\n"%DV%\\devcon.exe" remove ROOT\\ttinput* >nul 2>&1\r\nsc delete ttinputhid >nul 2>&1\r\ntimeout /t 3 /nobreak >nul\r\n"%DV%\\devcon.exe" install "%DV%\\ttinput.inf" ROOT\\ttinput >> "%~dp0安装记录.txt" 2>&1\r\nif %errorlevel% equ 0 (echo [OK] 完成 & timeout /t 2 >nul & del "%~dp0安装记录.txt" >nul 2>&1 & del "%~f0" & exit /b 0)\r\necho 安装失败, 详情见 安装记录.txt; 重启电脑后重开软件再试\r\ntimeout /t 5 >nul\r\ndel "%~f0"\r\n'
        try:
            with open(install_bat, 'w', encoding='gbk') as stream:
                stream.write(script)
            result = ctypes.windll.shell32.ShellExecuteW(None, 'runas', 'cmd.exe', f'/c ""{install_bat}""', SCRIPT_DIR, 0)
            if result > 32:
                state = '已停止' if service_stopped else '未安装'
                self._after_queue.put((self._log, (f'[驱动] 服务{state}，已请求管理员安装驱动，稍后自动生效',)))
            else:
                self._after_queue.put((self._log, ('[驱动] 安装被取消(需要管理员权限)，可稍后重启软件自动完成',)))
                try:
                    os.remove(install_bat)
                except OSError:
                    pass
        except Exception as exc:
            self._after_queue.put((self._log, (f'[驱动] 自检异常: {exc}',)))

    def _bind_foreground(self):
        hwnd = win32gui.GetForegroundWindow()
        if not hwnd or hwnd == self.root.winfo_id():
            self._alert('绑定', '请先切到游戏窗口，再点击绑定')
            return
        title = win32gui.GetWindowText(hwnd)
        self.settings['bind_hwnd'] = int(hwnd)
        self.settings['bind_title'] = title
        save_settings(self.settings)
        self.bind_label.config(text=title)
        self._drop_ui_mem()
        self._show_bind_highlight(hwnd)

    def _auto_bind(self):
        title = self.settings.get('bind_title', '')
        hwnd = find_window_by_title(title)
        if hwnd:
            self.settings['bind_hwnd'] = hwnd
            save_settings(self.settings)
            return hwnd
        return 0

    def _unlock_mouse(self):
        unlock_all_mouse()
        if self.runner:
            self.runner.set_mouse_lock(False)
        self._float_blink('鼠标已解锁', '#22c55e')

    def _auto_bind_loop(self):
        while not self._closing:
            try:
                hwnd = self.settings.get('bind_hwnd', 0)
                if hwnd and (not win32gui.IsWindow(hwnd)):
                    self._auto_bind()
            except Exception:
                pass
            time.sleep(5)

    def _start(self):
        if self._starting or self._running:
            return
        if not self._current_script:
            self._alert('启动', '请先选择驱动脚本')
            return
        self._do_start()

    def _do_start(self):
        self._starting = True
        key = (self.settings.get('activate_key') or App._act_key or '').strip()
        if not key:
            self._starting = False
            if self._show_activate_dialog():
                self._verify_ok_continue()
            return
        App._act_key = key

        def verify():
            ok, reason, _response = App._online_verify_silent(key)
            if ok:
                self._after_queue.put((self._verify_ok_continue, ()))
            else:
                self._after_queue.put((self._on_build_fail, (f'激活验证失败: {reason}', self._gen)))
        threading.Thread(target=verify, daemon=True).start()

    def _verify_ok_continue(self):
        self._launch_runner()

    def _launch_runner(self, retry=False):
        try:
            path = os.path.join(SCRIPTS_DIR, self._current_script)
            source = lua_read_text(path)
            self._gen += 1
            runner = LuaRunner(source, log_cb=self._log, status_cb=self._status, input_mode=self.settings.get('input_mode', 'KEDriver'), app=self)
            runner.set_config({'color_checks': self.settings.get('color_rules', {}).get(self._current_script, {}), 'config': self.settings})
            self.runner = runner
            self._runner_thread = threading.Thread(target=runner.run, daemon=True, name='ke_lua_runner')
            self._runner_thread.start()
            self._running = True
            self._starting = False
            self._refresh_driver_ui()
            self._status('运行中')
            self._float_blink('KeDriver已开启', '#10b981')
            tts_speak_func('KeDriver已开启')
            self._telemetry('start', self._current_script)
        except Exception as exc:
            self._on_build_fail(str(exc), self._gen)

    def _on_build_fail(self, msg, gen=None):
        if gen is not None and gen != self._gen:
            return
        self._starting = False
        self._running = False
        self._status('启动失败')
        self._log(f'启动失败: {msg}')
        self._refresh_driver_ui()

    def _retry_launch(self, gen):
        if gen == self._gen and (not self._closing):
            self._launch_runner(retry=True)

    def _stop(self):
        self._gen += 1
        runner = self.runner
        self.runner = None
        if runner:
            try:
                runner.stop()
            except Exception as exc:
                self._log(f'停止异常: {exc}')
        self._running = False
        self._starting = False
        self._refresh_driver_ui()
        self._status('已停止')
        self._float_blink('KeDriver已关闭', '#ef4444')
        tts_speak_func('KeDriver已关闭')
        self._telemetry('stop', self._current_script)

    def _force_reset(self):
        self._stop()
        reset_dxcam()
        self._drop_ui_mem()

    def _telemetry(self, event, script='', error='', duration=0):
        App._send_telemetry(event, script, error, duration)

    def _on_close(self):
        if self._closing:
            return
        self._closing = True
        try:
            self.settings['window_geo'] = self.root.geometry()
            save_settings(self.settings)
        except Exception:
            pass
        try:
            self._stop()
        except Exception:
            pass
        self._drop_ui_mem()
        unlock_all_mouse()
        try:
            self.root.destroy()
        except Exception:
            pass

    def _safe_after(self, ms, fn, *args):
        if threading.current_thread() is threading.main_thread():
            __temp_5421 = [ms, fn]
            __temp_5421.extend(args)
            return self.root.after(*tuple(__temp_5421))
        if self._after_queue.qsize() < 500:
            self._after_queue.put((ms, fn, args))
        else:
            _d = getattr(self, '_after_q_dropped', 0) + 1
            self._after_q_dropped = _d
            if not _d == 1:
                if _d % 200 == 0:
                    self._log('[队列] 子线程回调风暴: after队列满(水位500)已丢弃' + str(_d) + '条, 检查异常循环')
            else:
                self._log('[队列] 子线程回调风暴: after队列满(水位500)已丢弃' + str(_d) + '条, 检查异常循环')
        return None

    @classmethod
    def _mt(cls, fn, *args):
        try:
            if cls._mt_queue.qsize() < 500:
                cls._mt_queue.put((fn, args))
        except Exception:
            pass

    def _poll_after_queue(self):
        if self._closing:
            return
        while True:
            try:
                fn, args = App._mt_queue.get_nowait()
            except queue.Empty:
                break
            try:
                fn(*args)
            except Exception as exc:
                print(f'[DD._mt队列] {exc!r}')
        while True:
            try:
                item = self._after_queue.get_nowait()
            except queue.Empty:
                break
            try:
                if len(item) == 3:
                    ms, fn, args = item
                    self.root.after(ms, fn, *args)
                else:
                    fn, args = item
                    fn(*args)
            except Exception as exc:
                print(f'[UI queue] {exc!r}')
        try:
            self._poll_after_timer = self.root.after(100, self._poll_after_queue)
        except Exception:
            self._poll_after_timer = None

    def _log(self, msg):
        text = str(msg)
        line = time.strftime('%H:%M:%S') + ' ' + text
        with self._log_lock:
            self._log_lines.append(line)
            if len(self._log_lines) > 500:
                self._log_lines = self._log_lines[-300:]
        try:
            os.makedirs(os.path.dirname(os.path.join(SCRIPT_DIR, '日志.txt')), exist_ok=True)
            with open(os.path.join(SCRIPT_DIR, '日志.txt'), 'a', encoding='utf-8') as stream:
                stream.write(time.strftime('%Y-%m-%d ') + line + '\n')
        except Exception:
            pass
        if hasattr(self, 'root'):
            self._after_queue.put((self._append_log_gui, (line, text)))

    def _append_log_gui(self, line, msg):
        try:
            self.log_area.config(state='normal')
            tag = None
            if '[锁定]' in msg:
                tag = 'pass'
            elif '[闪避]' in msg:
                tag = 'dodge'
            elif '[战斗]' in msg:
                tag = 'fight'
            elif '[拾取]' in msg:
                tag = 'loot'
            elif '[验证码]' in msg:
                tag = 'captcha_crop'
            elif '[输入框]' in msg:
                tag = 'captcha_input'
            elif '[确认]' in msg:
                tag = 'captcha_ok'
            elif '错误' in msg:
                tag = 'fail'
            elif '⚠' in msg:
                tag = 'warn'
            self.log_area.insert(
                'end', line + '\n', (tag, 'hang') if tag else ('hang',)
            )
            try:
                if int(self.log_area.index('end-1c').split('.')[0]) > 800:
                    self.log_area.delete('1.0', '200.0')
            except Exception:
                pass
            self.log_area.see('end')
            self.log_area.config(state='disabled')
        except Exception as exc:
            print(f'[log GUI] {exc}')

    def _float_blink(self, text, color='#00BCD4'):
        color = {
            '#FF9800': '#f59e0b',
            '#FFD700': '#f59e0b',
            '#F59E0B': '#f59e0b',
            '#00BCD4': '#3fb950',
            '#10B981': '#3fb950',
            '#FF2A55': '#ff2a55',
            '#F85149': '#f85149',
            '#888': '#9d9d9d',
            '#999': '#9d9d9d',
            '#AAA': '#9d9d9d',
        }.get(str(color).upper(), color)
        try:
            if threading.current_thread() is not threading.main_thread():
                self._safe_after(0, self._float_blink, text, color)
                return
            if not hasattr(self, '_fw') or not self._fw:
                return
            if self._fw.state() == 'withdrawn':
                self._fw.deiconify()
                self.settings['float_show'] = True
                save_settings(self.settings)
            if not self._float_lbl or not self._float_lbl.winfo_exists():
                return
            self._float_lbl.config(text=text, fg=color)
            self._fw.update_idletasks()
            try:
                height = self._fw.winfo_height() or self._fw.winfo_reqheight()
                width = self._float_lbl.winfo_reqwidth() + 70
                self._fw.geometry(
                    f'{width}x{height}+{self._fw.winfo_x()}+{self._fw.winfo_y()}'
                )
            except BaseException:
                pass
        except BaseException:
            pass

    def _status(self, s):
        try:
            if threading.current_thread() is not threading.main_thread():
                self._safe_after(0, self._status, s)
                return
            self.status_text.config(text=s)
            if (
                hasattr(self, '_float_lbl')
                and self._float_lbl
                and self._float_lbl.winfo_exists()
            ):
                if s in ('running', '运行中'):
                    self._float_lbl.config(text='运行中', fg='#3fb950')
                else:
                    self._float_lbl.config(text='已停止', fg=POP_SUB)
        except Exception as exc:
            print(f'[DD.float_status] {exc}')

    def _show_bind_highlight(self, hwnd=None):
        hwnd = hwnd or self.settings.get('bind_hwnd', 0)
        if not hwnd:
            if getattr(self, '_hl_win', None):
                try:
                    self._hl_win.destroy()
                except BaseException:
                    pass
                self._hl_win = None
            if getattr(self, '_hl_timer', None):
                try:
                    self.root.after_cancel(self._hl_timer)
                except BaseException:
                    pass
                self._hl_timer = None
            return
        if getattr(self, '_hl_win', None):
            try:
                self._hl_win.destroy()
            except BaseException:
                pass
            self._hl_win = None
        if getattr(self, '_hl_timer', None):
            try:
                self.root.after_cancel(self._hl_timer)
            except BaseException:
                pass
            self._hl_timer = None
        if not win32gui.IsWindow(hwnd):
            return

        def draw():
            try:
                if not win32gui.IsWindow(hwnd):
                    if getattr(self, '_hl_win', None):
                        try:
                            self._hl_win.destroy()
                        except BaseException:
                            pass
                        self._hl_win = None
                    return
                rect = win32gui.GetWindowRect(hwnd)
                if rect[2] - rect[0] <= 0 or rect[3] - rect[1] <= 0:
                    self._hl_timer = self.root.after(500, draw)
                    return
                x, y, width, height = (
                    rect[0], rect[1], rect[2] - rect[0], rect[3] - rect[1]
                )
                if not getattr(self, '_hl_win', None):
                    self._hl_win = tk.Toplevel(self.root)
                    self._hl_win.overrideredirect(True)
                    self._hl_win.attributes('-topmost', True, '-alpha', 0.35)
                    self._hl_win.configure(bg='#00FF00')
                self._hl_win.geometry(f'{width}x{height}+{x}+{y}')
            except BaseException:
                pass
            self._hl_timer = self.root.after(500, draw)

        draw()

    def _quick_capture(self, mode):
        if hasattr(self, '_wiz_names'):
            del self._wiz_names
        self._cap_mode = '' if mode == 'point' else mode
        mode_name = {'point': '取色', 'ocr': '取字', 'img': '取图'}.get(mode, mode)
        self._log(f'模式: {mode_name}，框选目标区域')
        self._start_region_selector()

    def _start_region_selector(self):
        if getattr(self, '_capturing', False):
            return
        self._capturing = True
        try:
            unlock_all_mouse()
        except Exception:
            pass
        hwnd = self.settings.get('bind_hwnd', 0) or getattr(self, '_game_hwnd', 0)
        try:
            rect = win32gui.GetWindowRect(int(hwnd)) if hwnd and win32gui.IsWindow(int(hwnd)) else None
            if rect and (rect[2] - rect[0] < 50 or rect[3] - rect[1] < 50 or rect[0] < -10000):
                rect = None
        except Exception:
            rect = None
        if rect is None:
            left = top = 0
            right = self.root.winfo_screenwidth()
            bottom = self.root.winfo_screenheight()
            rect = (left, top, right, bottom)
        left, top, right, bottom = rect
        width, height = (right - left, bottom - top)
        self._cap_rect = rect
        try:
            screenshot = ImageGrab.grab((left, top, right, bottom)).convert('RGB')
        except Exception as exc:
            self._capturing = False
            self._log(f'[截图] {exc}')
            return
        overlay = tk.Toplevel(self.root)
        overlay.overrideredirect(True)
        overlay.geometry(f'{width}x{height}+{left}+{top}')
        overlay.attributes('-topmost', True)
        overlay.configure(bg='#0b1220')
        canvas = tk.Canvas(overlay, width=width, height=height, highlightthickness=0, cursor='none')
        canvas.pack(fill='both', expand=True)
        image_ref = ImageTk.PhotoImage(screenshot)
        canvas.create_image(0, 0, image=image_ref, anchor='nw')
        canvas.image = image_ref
        canvas.create_text(width // 2, height - 28, text='拖拽框选检测区域  ·  滚轮缩放  ·  Esc 取消', fill='#eeeeee', font=('Microsoft YaHei UI', 10), tags='fixed_tip')
        selection = {'start': None, 'id': None}
        zoom_levels = [2, 3, 4, 6, 8, 10]
        zoom_index = [1]
        image_array = np.array(screenshot)

        def draw_magnifier(event=None):
            canvas.delete('magnifier')
            mx = event.x if event is not None else overlay.winfo_pointerx() - overlay.winfo_rootx()
            my = event.y if event is not None else overlay.winfo_pointery() - overlay.winfo_rooty()
            mx = max(0, min(width - 1, int(mx)))
            my = max(0, min(height - 1, int(my)))
            canvas.create_line(0, my, width, my, fill='#1e3a8a', width=1, dash=(2, 3), tags='magnifier')
            canvas.create_line(mx, 0, mx, height, fill='#1e3a8a', width=1, dash=(2, 3), tags='magnifier')
            half = 15
            px = max(half, min(image_array.shape[1] - half - 1, mx))
            py = max(half, min(image_array.shape[0] - half - 1, my))
            roi = image_array[py - half:py + half, px - half:px + half]
            if roi.size == 0:
                return
            zoom = zoom_levels[zoom_index[0]]
            cell = max(3, zoom * 2)
            roi_height, roi_width = roi.shape[:2]
            magnified = Image.fromarray(roi).resize((roi_width * cell, roi_height * cell), Image.Resampling.NEAREST)
            drawing = ImageDraw.Draw(magnified)
            for column in range(1, roi_width):
                drawing.line((column * cell, 0, column * cell, roi_height * cell), fill=(50, 50, 50), width=1)
            for row in range(1, roi_height):
                drawing.line((0, row * cell, roi_width * cell, row * cell), fill=(50, 50, 50), width=1)
            center_x, center_y = (roi_width // 2, roi_height // 2)
            color = tuple((int(value) for value in roi[center_y, center_x, :3]))
            drawing.rectangle((center_x * cell, center_y * cell, (center_x + 1) * cell - 1, (center_y + 1) * cell - 1), outline=color, width=2)
            brightness = (color[0] * 299 + color[1] * 587 + color[2] * 114) // 1000
            cross_color = (0, 0, 0) if brightness > 128 else (255, 255, 255)
            cx = center_x * cell + cell // 2
            cy = center_y * cell + cell // 2
            drawing.line((cx - 6, cy, cx + 6, cy), fill=cross_color, width=max(1, cell // 4))
            drawing.line((cx, cy - 6, cx, cy + 6), fill=cross_color, width=max(1, cell // 4))
            canvas._magtk = ImageTk.PhotoImage(magnified)
            mag_width, mag_height = (roi_width * cell, roi_height * cell)
            mag_x, mag_y = (mx + 30, my + 30)
            if mag_x + mag_width > width:
                mag_x = mx - mag_width - 30
            if mag_y + mag_height > height:
                mag_y = my - mag_height - 30
            mag_x, mag_y = (max(4, mag_x), max(4, mag_y))
            canvas.create_image(mag_x, mag_y, image=canvas._magtk, anchor='nw', tags='magnifier')
            canvas.create_rectangle(mag_x - 2, mag_y - 2, mag_x + mag_width + 2, mag_y + mag_height + 2, outline='#FF9800', width=2, tags='magnifier')
            info = f'RGB({color[0]},{color[1]},{color[2]})  ({px},{py})'
            text_width = len(info) * 7 + 12
            info_y = my - 40 if my >= 45 else my + 12
            canvas.create_rectangle(mx + 28, info_y, mx + 28 + text_width, info_y + 21, fill='#0f172a', outline='#444', tags='magnifier')
            canvas.create_text(mx + 34, info_y + 10, text=info, fill='#00ff66', font=('Consolas', 10, 'bold'), anchor='w', tags='magnifier')
            canvas.create_text(mag_x + 5, mag_y + 5, text=f'滚轮 {zoom}x', fill='#FF9800', font=('Consolas', 9, 'bold'), anchor='nw', tags='magnifier')
            if selection['id']:
                canvas.tag_raise(selection['id'])

        def close():
            self._capturing = False
            try:
                overlay.destroy()
            except Exception:
                pass

        def down(event):
            selection['start'] = (event.x, event.y)
            if selection['id']:
                canvas.delete(selection['id'])
            selection['id'] = canvas.create_rectangle(event.x, event.y, event.x, event.y, outline='#00e5ff', width=2)

        def move(event):
            draw_magnifier(event)
            if selection['start'] and selection['id']:
                x, y = selection['start']
                canvas.coords(selection['id'], x, y, event.x, event.y)

        def wheel(event):
            if event.delta > 0:
                zoom_index[0] = min(len(zoom_levels) - 1, zoom_index[0] + 1)
            else:
                zoom_index[0] = max(0, zoom_index[0] - 1)
            draw_magnifier(event)

        def up(event):
            if not selection['start']:
                return
            x0, y0 = selection['start']
            x1, y1 = (event.x, event.y)
            sx, sy = (min(x0, x1), min(y0, y1))
            sw, sh = (abs(x1 - x0), abs(y1 - y0))
            if sw < 2 or sh < 2:
                selection['start'] = None
                return
            crop = screenshot.crop((sx, sy, sx + sw, sy + sh))
            screen_x, screen_y = (left + sx, top + sy)
            close()
            self._show_region(screen_x, screen_y, sw, sh, width, height, screenshot, rect)
        canvas.bind('<ButtonPress-1>', down)
        canvas.bind('<B1-Motion>', move)
        canvas.bind('<ButtonRelease-1>', up)
        canvas.bind('<Motion>', draw_magnifier)
        canvas.bind('<MouseWheel>', wheel)
        overlay.bind('<MouseWheel>', wheel)
        overlay.bind('<Escape>', lambda _event: close())
        overlay.protocol('WM_DELETE_WINDOW', close)
        overlay.focus_force()
        draw_magnifier()

    def _register_img_rule(self, name):
        if not name or not self._current_script:
            return
        stem = os.path.splitext(os.path.basename(str(name)))[0]
        thresholds = self.settings.setdefault('img_thresholds', {}).setdefault(self._current_script, {})
        thresholds.setdefault(stem, 95)
        enabled = self.settings.setdefault('img_rules_enabled', {}).setdefault(self._current_script, {})
        enabled.setdefault(stem, True)
        save_settings(self.settings)

    def _do_capture_img(self, x, y, w, h, save=True, name=None, region=None):
        try:
            raw = ImageGrab.grab((x, y, x + w, y + h)).convert('RGB')
            image = np.array(raw)[:, :, :3]
            editor = self._capture_edit(image, auto_name=name)
            if region and name and self._current_script:
                stem = os.path.splitext(str(name))[0]
                regions = self.settings.setdefault('img_rules_regions', {}).setdefault(self._current_script, {})
                regions[stem] = region
                save_settings(self.settings)
                self._log(f"[图] '{stem}' 检测区域: x{region['x_pct']}% y{region['y_pct']}% {region['w_pct']}%x{region['h_pct']}%")
            return editor
        except Exception as exc:
            self._log(f'取图异常: {exc}')
            return None

    def _capture_edit(self, img_rgb, auto_name=None):
        """Open the original-style crop editor with wheel zoom and three mask modes."""
        height, width = img_rgb.shape[:2]
        if height < 1 or width < 1:
            return None
        scale = [min(max(800 / width, 600 / height, 2.0), 20.0)]
        mode = ['lasso']
        modes = {'rect': '矩形', 'lasso': '描边', 'auto': '自动'}
        name_state = [auto_name]
        rect_start = [None]
        rect_end = [None]
        points = []
        drawing = [False]
        closed = [False]
        editor = tk.Toplevel(self.root)
        editor.title(f'抠图[{modes[mode[0]]}]' + (f'-{auto_name}' if auto_name else ''))
        editor.configure(bg='#1a1a2e')
        editor.attributes('-topmost', True)
        editor.lift()
        editor.focus_force()
        button_frame = tk.Frame(editor, bg='#1a1a2e')
        button_frame.pack(pady=(8, 0))
        buttons = {}
        canvas = tk.Canvas(editor, bg='#000000', highlightthickness=0, cursor='crosshair')
        canvas.pack(padx=10, pady=(8, 0))
        hint = tk.Label(editor, fg='#94a3b8', bg='#1a1a2e', font=('Microsoft YaHei UI', 10))
        hint.pack(pady=6)

        def view_size():
            return (max(1, int(width * scale[0])), max(1, int(height * scale[0])))

        def image_xy(event_x, event_y):
            return (max(0, min(width - 1, int(canvas.canvasx(event_x) / scale[0]))), max(0, min(height - 1, int(canvas.canvasy(event_y) / scale[0]))))

        def canvas_xy(point):
            return (point[0] * scale[0], point[1] * scale[0])

        def update_hint(message=None):
            editor.title(f'抠图[{modes[mode[0]]}]' + (f'-{name_state[0]}' if name_state[0] else ''))
            hint.config(text=message or f'{modes[mode[0]]}模式 | 缩放{scale[0]:.1f}x | 滚轮缩放 | 回车保存 | ESC取消 | Tab切模式')

        def redraw_selection():
            canvas.delete('selection')
            if mode[0] == 'rect' and rect_start[0] and rect_end[0]:
                x0, y0 = canvas_xy(rect_start[0])
                x1, y1 = canvas_xy(rect_end[0])
                canvas.create_rectangle(x0, y0, x1, y1, outline='#ff0040', width=4, tags='selection')
            elif mode[0] == 'lasso' and len(points) >= 2:
                flat = []
                for point in points:
                    flat.extend(canvas_xy(point))
                canvas.create_line(*flat, fill='#ff0040', width=4, tags='selection')
                if closed[0] and len(points) >= 3:
                    x0, y0 = canvas_xy(points[-1])
                    x1, y1 = canvas_xy(points[0])
                    canvas.create_line(x0, y0, x1, y1, fill='#ff0040', width=4, tags='selection')

        def redraw_image():
            out_width, out_height = view_size()
            display = cv2.resize(img_rgb, (out_width, out_height), interpolation=cv2.INTER_NEAREST)
            canvas.config(width=min(out_width, 1550), height=min(out_height, 790), scrollregion=(0, 0, out_width, out_height))
            canvas.delete('image')
            canvas._photo = ImageTk.PhotoImage(Image.fromarray(display))
            canvas.create_image(0, 0, image=canvas._photo, anchor='nw', tags='image')
            canvas.tag_lower('image')
            canvas.delete('grid')
            if scale[0] >= 4 and width <= 500 and (height <= 500):
                for column in range(1, width):
                    x = int(column * scale[0])
                    canvas.create_line(x, 0, x, out_height, fill='#292929', width=1, tags='grid')
                for row in range(1, height):
                    y = int(row * scale[0])
                    canvas.create_line(0, y, out_width, y, fill='#292929', width=1, tags='grid')
            editor.geometry(f'{min(out_width + 40, 1600)}x{min(out_height + 125, 950)}')
            redraw_selection()
            update_hint()

        def reset_selection():
            rect_start[0] = rect_end[0] = None
            points.clear()
            drawing[0] = closed[0] = False
            canvas.delete('selection')

        def switch(new_mode, _button=None):
            mode[0] = new_mode
            reset_selection()
            for key, button in buttons.items():
                button.config(relief='sunken' if key == new_mode else 'flat')
            update_hint()
            if new_mode == 'auto':
                auto_detect()
        for key, color in (('rect', '#2196F3'), ('lasso', '#ff0040'), ('auto', '#10b981')):
            button = tk.Label(button_frame, text=modes[key], fg='white', bg=color, cursor='hand2', font=('Microsoft YaHei UI', 10, 'bold'), padx=10, pady=3, relief='sunken' if key == mode[0] else 'flat')
            button.pack(side='left', padx=2)
            button.bind('<Button-1>', lambda _event, selected=key, control=button: switch(selected, control))
            buttons[key] = button

        def down(event):
            if mode[0] == 'auto':
                return
            point = image_xy(event.x, event.y)
            reset_selection()
            drawing[0] = True
            if mode[0] == 'rect':
                rect_start[0] = rect_end[0] = point
            else:
                points.append(point)
            redraw_selection()

        def move(event):
            if not drawing[0]:
                return
            point = image_xy(event.x, event.y)
            if mode[0] == 'rect':
                rect_end[0] = point
            elif not points or point != points[-1]:
                points.append(point)
            redraw_selection()

        def up(_event):
            if not drawing[0]:
                return
            drawing[0] = False
            if mode[0] == 'lasso' and len(points) >= 3:
                closed[0] = True
                update_hint('已闭合! 回车保存 | 按住左键重画 | ESC取消')
            elif mode[0] == 'rect' and rect_start[0] and rect_end[0]:
                closed[0] = True
                update_hint('已选矩形! 回车保存 | 按住左键重选 | ESC取消')
            redraw_selection()

        def wheel(event):
            scale[0] = min(25.0, scale[0] * 1.3) if event.delta > 0 else max(1.0, scale[0] / 1.3)
            redraw_image()

        def output_name():
            value = name_state[0]
            if not value:
                value = simpledialog.askstring('命名', '模板名称:', parent=editor)
            value = re.sub('[\\\\/:*?"<>|]', '_', str(value or '')).strip()
            if not value:
                value = f'cap_{int(time.time() * 1000000)}'
            value = os.path.splitext(value)[0]
            name_state[0] = value
            return value

        def save_mask(mask, label):
            directory = os.path.join(SCRIPT_DIR, '图库')
            os.makedirs(directory, exist_ok=True)
            name = output_name()
            mask = cv2.GaussianBlur(mask.astype(np.uint8), (3, 3), 0)
            rgba = np.dstack((img_rgb[:, :, :3], mask))
            path = os.path.join(directory, f'{name}.png')
            Image.fromarray(rgba, 'RGBA').save(path)
            self._log(f'{label}已保存: 图库/{name}.png ({width}x{height})')
            self._register_img_rule(name)
            self._refresh_lib_if_open()
            editor.destroy()
            return path

        def auto_detect():
            corners = np.array([img_rgb[0, 0], img_rgb[0, -1], img_rgb[-1, 0], img_rgb[-1, -1], img_rgb[height // 2, 0], img_rgb[height // 2, -1], img_rgb[0, width // 2], img_rgb[-1, width // 2]])
            background = np.median(corners, axis=0).astype(int)
            difference = np.abs(img_rgb.astype(int) - background).max(axis=2)
            mask = (difference > 30).astype(np.uint8) * 255
            kernel = cv2.getStructuringElement(cv2.MORPH_ELLIPSE, (5, 5))
            mask = cv2.morphologyEx(mask, cv2.MORPH_CLOSE, kernel)
            mask = cv2.morphologyEx(mask, cv2.MORPH_OPEN, kernel)
            self._log(f'自动检测: 背景RGB({background[0]},{background[1]},{background[2]})')
            save_mask(mask, '自动抠图')

        def save_selection():
            if not closed[0]:
                update_hint('请先拖出矩形或描边区域')
                return
            mask = np.zeros((height, width), dtype=np.uint8)
            if mode[0] == 'rect' and rect_start[0] and rect_end[0]:
                x0, x1 = sorted((rect_start[0][0], rect_end[0][0]))
                y0, y1 = sorted((rect_start[0][1], rect_end[0][1]))
                mask[max(0, y0):min(height, y1 + 1), max(0, x0):min(width, x1 + 1)] = 255
            elif mode[0] == 'lasso' and len(points) >= 3:
                polygon = np.array(points, dtype=np.int32).reshape((-1, 1, 2))
                cv2.fillPoly(mask, [polygon], 255)
            save_mask(mask, '抠图')

        def keypress(event):
            if event.keysym == 'Tab':
                order = list(modes)
                switch(order[(order.index(mode[0]) + 1) % len(order)])
            elif event.keysym == 'Return':
                save_selection()
            elif event.keysym == 'Escape':
                editor.destroy()
        canvas.bind('<ButtonPress-1>', down)
        canvas.bind('<B1-Motion>', move)
        canvas.bind('<ButtonRelease-1>', up)
        canvas.bind('<MouseWheel>', wheel)
        editor.bind('<Key>', keypress)
        redraw_image()
        editor.focus_set()
        self._log('抠图: Tab切模式(矩形/描边/自动) | 滚轮缩放 | 回车保存')
        return editor

    def _do_ocr(self, x, y, w, h, save=True):
        image = np.array(ImageGrab.grab((x, y, x + w, y + h)))[:, :, :3][:, :, ::-1]
        result = ocr_image(image)
        if result:
            self._log(f'OCR结果: {result}')
            if save:
                directory = os.path.join(SCRIPT_DIR, '文库')
                os.makedirs(directory, exist_ok=True)
                stamp = str(int(time.time() * 1000))
                image_name = f'ocr_{stamp}.png'
                Image.fromarray(image[:, :, ::-1]).save(os.path.join(directory, image_name))
                with open(os.path.join(directory, f'ocr_{stamp}.json'), 'w', encoding='utf-8') as stream:
                    json.dump({'text': result, 'image': image_name, 'region': [x, y, w, h], 'time': time.strftime('%H:%M:%S')}, stream, ensure_ascii=False, indent=2)
                self._log(f'取字已保存: 文库/{image_name} → {result}')
        else:
            self._log('OCR: 未识别到文字')
        self._alert('OCR', result or '未识别到文字')
        return result

    def _show_region(self, sx, sy, sw, sh, sw_s, sh_s, pil_img, r):
        self._log(f'区域: ({sx},{sy}) {sw}x{sh}')
        left, top = (r[0], r[1])
        rx = round((sx - left) / max(sw_s, 1) * 100, 2)
        ry = round((sy - top) / max(sh_s, 1) * 100, 2)
        rw = round(sw / max(sw_s, 1) * 100, 2)
        rh = round(sh / max(sh_s, 1) * 100, 2)
        array = np.array(pil_img)
        x0, y0 = (max(0, sx - left), max(0, sy - top))
        cap = array[y0:y0 + sh, x0:x0 + sw].copy()
        if cap.size == 0:
            self._log('截图区域为空')
            return
        pixels = cap[:, :, :3].astype(np.int32)
        saturation = pixels.max(axis=2) - pixels.min(axis=2)
        index = int(saturation.argmax())
        best = pixels[index // pixels.shape[1], index % pixels.shape[1]]
        red, green, blue = (int(value) for value in best)
        self._log(f'({rx}%,{ry}%) {rw}%x{rh}% RGB({red},{green},{blue})')
        mode = getattr(self, '_cap_mode', 'color')
        names = getattr(self, '_wiz_names', [])
        wizard_index = getattr(self, '_wizard_step', 0)
        wizard = wizard_index < len(names)
        name = names[wizard_index] if wizard else None
        if wizard:
            self._test_on_region(name, cap, red, green, blue)
        if mode == 'ocr':
            self._do_ocr(sx, sy, sw, sh, save=wizard)
        elif mode == 'img':
            region = {'x_pct': rx, 'y_pct': ry, 'w_pct': rw, 'h_pct': rh}
            self._do_capture_img(sx, sy, sw, sh, save=wizard, name=name, region=region)
        elif wizard:
            self._auto_save(rx, ry, rw, rh, cap, name=name)
        else:
            self._quick_color_info(cap)
        if wizard:
            self._safe_after(200, self._wiz_next)

    def _popup_check(self, key):
        window = self._popup_windows.get(key)
        return bool(window and window.winfo_exists())

    def _popup_register(self, pw, key, on_close=None):
        self._popup_windows[key] = pw
        setattr(self, f'_popup_{key}', pw)
        try:
            unlock_all_mouse()
        except Exception:
            pass

        def close():
            self._popup_windows.pop(key, None)
            setattr(self, f'_popup_{key}', None)
            self._popup_save_geo(pw, key)
            if on_close:
                on_close()
            pw.destroy()
            try:
                if self._running and self.runner:
                    self.runner.set_mouse_lock(True)
            except Exception:
                pass
        pw.protocol('WM_DELETE_WINDOW', close)

    def _popup_snap(self, pw, key, w, h, lock_size=False):
        geometry = self.settings.get(f'popup_{key}_geo') or self.settings.get(f'popup_geo_{key}')
        if geometry and (not lock_size):
            try:
                size = geometry.split('+')[0]
                saved_width, saved_height = size.split('x', 1)
                w, h = (int(saved_width), int(saved_height))
            except Exception:
                pass
        try:
            x = max(0, self.root.winfo_x() - w)
            y = max(0, self.root.winfo_y() + self.root.winfo_height() - h)
            pw.geometry(f'{w}x{h}+{x}+{y}')
        except Exception:
            pw.geometry(f'{w}x{h}')
        pw.resizable(not lock_size, not lock_size)
        if lock_size:
            pw.pack_propagate(False)

    def _popup_save_geo(self, pw, key):
        try:
            self.settings[f'popup_{key}_geo'] = pw.geometry()
            save_settings(self.settings)
        except Exception:
            pass

    def run(self):
        self._log('KE 外设已启动')
        self._check_autostart()
        try:
            import ke_collect
            ke_collect.start_collector(lambda: load_settings())
        except Exception:
            pass
        self._safe_after(500, self._refresh_ai_card)
        self._safe_after(500, self._mem_loop)
        self.root.mainloop()

    def _refresh_ai_card(self):
        if self._closing:
            return
        state = get_ai_state()
        status = state.get('status') or '等待验证码'
        if hasattr(self, '_ai_lbl'):
            self._ai_lbl.config(text=f'验证码: {status}', fg=self._AI_COLORS['ok'] if '通过' in status or '已识别' in status else self._AI_COLORS['fail'] if '失败' in status else '#9ca3af')
        memory = get_mem_viz()
        if hasattr(self, '_ai_mem_lbl'):
            self._ai_mem_lbl.config(text=f"Mem: {('已连接' if memory.get('connected') else '未连接')}", fg=self._AI_COLORS['ok'] if memory.get('connected') else '#9ca3af')
        self._safe_after(500, self._refresh_ai_card)

    def _ai_flash_loop(self, lbl, tick):
        if tick <= 0:
            return
        try:
            lbl.config(fg=self._AI_COLORS['flash'] if tick % 2 else self._AI_COLORS['idle'])
            lbl.after(250, self._ai_flash_loop, lbl, tick - 1)
        except Exception:
            pass

    def _captcha_calibrate_manual(self, pick=None, ss_var=None, dialog_rect=None):
        if getattr(self, '_calibrating', False):
            return
        self._calibrating = True
        try:
            if self.runner and getattr(self.runner, '_mouse_locked', False):
                self.runner.suspend_inject(3600)
        except Exception:
            pass
        try:
            clip_cursor()
        except Exception:
            pass
        previous = copy.deepcopy(self.settings.get('captcha_cal', {}))
        calibration = self.settings.setdefault('captcha_cal', {})
        hwnd = int(self.settings.get('bind_hwnd', 0) or 0)
        screen_width = self.root.winfo_screenwidth()
        screen_height = self.root.winfo_screenheight()
        try:
            rect = win32gui.GetWindowRect(hwnd) if hwnd and win32gui.IsWindow(hwnd) else None
            if rect and (rect[2] - rect[0] < 100 or rect[3] - rect[1] < 100 or rect[0] < -10000):
                rect = None
        except Exception:
            rect = None
        if rect:
            wx, wy, right, bottom = rect
            ww, wh = (right - wx, bottom - wy)
        else:
            wx = wy = 0
            ww, wh = (screen_width, screen_height)
        try:
            screenshot = ImageGrab.grab().convert('RGB')
        except Exception as exc:
            self._calibrating = False
            self._log(f'[打码] 校准截图失败: {exc}')
            return
        window = tk.Toplevel(self.root)
        window.overrideredirect(True)
        window.geometry(f'{screen_width}x{screen_height}+0+0')
        window.attributes('-topmost', True)
        canvas = tk.Canvas(window, bg='#111', cursor='crosshair', highlightthickness=0)
        canvas.pack(fill='both', expand=True)
        background = ImageTk.PhotoImage(screenshot)
        canvas.create_image(0, 0, image=background, anchor='nw')
        canvas.image = background
        try:
            canvas.create_rectangle(wx, wy, wx + ww, wy + wh, outline='#facc15', width=2)
        except Exception:
            pass
        steps = [('验证码区域', '#00bfff', 'crop'), ('输入框', '#00e676', 'input'), ('确认按钮', '#ff6d00', 'ok'), ('刷新按钮', '#e040fb', 'refresh')]
        step_index = [0]
        start_at = [None]
        active_rectangle = [None]
        drawn = []
        bar = tk.Frame(canvas, bg='#111827')
        canvas.create_window(screen_width // 2, 20, window=bar, anchor='n')
        label = tk.Label(bar, text='第1步: 拖画 验证码区域', font=('Microsoft YaHei UI', 14, 'bold'), fg=steps[0][1], bg='#111827')
        label.pack(side='left', padx=14, pady=9)
        tk.Label(bar, text=f"基准: ({wx},{wy}) {ww}x{wh} {('窗口' if rect else '全屏')}", fg='#9ca3af', bg='#111827').pack(side='left', padx=6)

        def update_label():
            if step_index[0] >= len(steps):
                label.config(text='完成，请点保存或测试', fg='#4ade80')
            else:
                name, color, _prefix = steps[step_index[0]]
                label.config(text=f'第{step_index[0] + 1}步: 拖画 {name}', fg=color)

        def clean(cancelled=False):
            if cancelled:
                self.settings['captcha_cal'] = previous
            self._calibrating = False
            try:
                if self.runner:
                    self.runner.resume_inject()
            except Exception:
                pass
            try:
                clip_cursor()
            except Exception:
                pass
            try:
                window.destroy()
            except Exception:
                pass

        def save():
            for prefix in ('crop', 'input', 'ok', 'refresh'):
                for suffix in ('x', 'y', 'w', 'h'):
                    calibration.setdefault(f'{prefix}_{suffix}', 0)
            save_settings(self.settings)
            self._log(f"[打码] crop=({calibration['crop_x']},{calibration['crop_y']},{calibration['crop_w']}x{calibration['crop_h']}) inp=({calibration['input_x']},{calibration['input_y']}) ok=({calibration['ok_x']},{calibration['ok_y']}) refresh=({calibration['refresh_x']},{calibration['refresh_y']})")
            clean()
        buttons = tk.Frame(bar, bg='#111827')
        buttons.pack(side='right', padx=6)
        tk.Button(buttons, text='保存', command=save, bg='#1f6feb', fg='white', relief='flat', width=6).pack(side='right', padx=2)
        tk.Button(buttons, text='取消', command=lambda: clean(True), bg='#ef4444', fg='white', relief='flat', width=6).pack(side='right', padx=2)
        tk.Button(buttons, text='测试', command=lambda: self._captcha_visual_test(canvas, calibration, wx, wy, ww, wh, steps, label, window, clean), bg='#f97316', fg='white', relief='flat', width=6).pack(side='right', padx=2)

        def down(event):
            if step_index[0] >= len(steps):
                return
            start_at[0] = (event.x_root, event.y_root)

        def move(event):
            if not start_at[0] or step_index[0] >= len(steps):
                return
            if active_rectangle[0]:
                canvas.delete(active_rectangle[0])
            _name, color, _prefix = steps[step_index[0]]
            x0, y0 = start_at[0]
            active_rectangle[0] = canvas.create_rectangle(x0, y0, event.x_root, event.y_root, outline=color, width=3, dash=(6, 3))

        def up(event):
            if not start_at[0] or step_index[0] >= len(steps):
                return
            if active_rectangle[0]:
                canvas.delete(active_rectangle[0])
                active_rectangle[0] = None
            x0, y0 = start_at[0]
            x1, y1 = (event.x_root, event.y_root)
            left, top = (min(x0, x1), min(y0, y1))
            width, height = (abs(x1 - x0), abs(y1 - y0))
            start_at[0] = None
            if width < 4 or height < 4:
                return
            name, color, prefix = steps[step_index[0]]
            x_percent = round((left - wx) / max(ww, 1) * 100, 2)
            y_percent = round((top - wy) / max(wh, 1) * 100, 2)
            w_percent = round(width / max(ww, 1) * 100, 2)
            h_percent = round(height / max(wh, 1) * 100, 2)
            calibration[f'{prefix}_x'] = x_percent
            calibration[f'{prefix}_y'] = y_percent
            calibration[f'{prefix}_w'] = w_percent
            calibration[f'{prefix}_h'] = h_percent
            drawn.append(canvas.create_rectangle(left, top, left + width, top + height, outline=color, width=3))
            self._log(f'[打码] {name}=({x_percent},{y_percent},{w_percent}x{h_percent})%')
            step_index[0] += 1
            update_label()
        canvas.bind('<ButtonPress-1>', down)
        canvas.bind('<B1-Motion>', move)
        canvas.bind('<ButtonRelease-1>', up)
        window.bind('<Escape>', lambda _event: clean(True))
        window.protocol('WM_DELETE_WINDOW', lambda: clean(True))
        window.focus_force()
        window.after(800, clip_cursor)

    def _captcha_visual_test(self, canvas=None, cc=None, wx=0, wy=0, ww=0, wh=0, steps=None, bl=None, cv=None, _clean=None):
        calibration = cc or self.settings.get('captcha_cal', {})
        ready = bool(calibration.get('crop_w') and calibration.get('input_x'))
        if canvas is None or bl is None or cv is None:
            return ready
        if not ready:
            bl.config(text='请先校准!', fg='#ef4444')
            return False
        for sequence in ('<ButtonPress-1>', '<B1-Motion>', '<ButtonRelease-1>'):
            canvas.unbind(sequence)
        try:
            hwnd = int(self.settings.get('bind_hwnd', 0) or 0)
            rect = win32gui.GetWindowRect(hwnd) if hwnd and win32gui.IsWindow(hwnd) else None
            if rect and rect[2] - rect[0] > 100 and (rect[3] - rect[1] > 100) and (rect[0] > -10000):
                wx, wy, ww, wh = (rect[0], rect[1], rect[2] - rect[0], rect[3] - rect[1])
        except Exception:
            pass
        test_items = []
        for item in getattr(self, '_test_boxes', []):
            try:
                canvas.delete(item)
            except Exception:
                pass
        self._test_boxes = test_items
        colors = ['#00bfff', '#00e676', '#ff6d00', '#e040fb']
        labels = ['截取验证码区域', '单击输入框 → Ctrl+V粘贴验证码', '单击确认按钮', '单击刷新按钮']
        index = [0]

        def percent_box(prefix):
            x = int(wx + ww * calibration.get(f'{prefix}_x', 0) / 100)
            y = int(wy + wh * calibration.get(f'{prefix}_y', 0) / 100)
            width = int(ww * calibration.get(f'{prefix}_w', 0) / 100)
            height = int(wh * calibration.get(f'{prefix}_h', 0) / 100)
            return (x, y, width, height)

        def run_step():
            i = index[0]
            if i >= 4:
                bl.config(text='视觉测试完成(仅演示, 未提交打码), 按Esc退出', fg='#4ade80')
                return
            prefix = ('crop', 'input', 'ok', 'refresh')[i]
            x, y, width, height = percent_box(prefix)
            color = colors[i]
            bl.config(text=f'第{i + 1}步: {labels[i]}', fg=color)
            if i == 0:
                item = canvas.create_rectangle(x, y, x + width, y + height, outline=color, width=5)
                cx, cy = (x + width // 2, y + height // 2)
            else:
                cx, cy = (x + width // 2, y + height // 2)
                item = canvas.create_oval(cx - 10, cy - 10, cx + 10, cy + 10, outline=color, fill=color)
            test_items.append(item)
            try:
                if self.runner and getattr(self.runner, 'dd', None):
                    self.runner.dd.move_to(cx, cy)
                else:
                    ctypes.windll.user32.SetCursorPos(cx, cy)
            except Exception:
                pass
            index[0] += 1
            cv.after(1500, run_step)
        bl.config(text='3秒后开始测试...', fg='#FF9800')
        cv.after(3000, run_step)
        return True

    @staticmethod
    def _get_stable_hwid():
        return stable_hwid()

    @staticmethod
    def _sign_cache(hwid, key):
        timestamp = str(int(time.time()))
        signature = hashlib.md5(f'{CACHE_SALT}|{hwid}|{key[:8]}|{timestamp}'.encode()).hexdigest()[:16]
        return f'{hwid}|{timestamp}|{signature}'

    @staticmethod
    def _online_verify_silent(key, name=''):
        data = json.dumps({'key': key, 'hwid': App._act_hwid, 'name': name}).encode()
        last_error = '无法连接激活服务器'
        for server in App._act_srv_list:
            if not server:
                continue
            try:
                request = urllib.request.Request(f'{server}/verify', data=data, headers={'Content-Type': 'application/json'})
                response = json.loads(urllib.request.urlopen(request, timeout=3).read())
                if response and response.get('ok') and _kc_verify(response, key, App._act_hwid):
                    App._act_ok = True
                    App._act_key = key
                    App._act_type = response.get('type', '')
                    App._act_exp = response.get('expires', '')
                    settings = load_settings()
                    settings['activate_key'] = key
                    settings['activate_type'] = App._act_type
                    settings['activate_exp'] = App._act_exp
                    settings['is_admin'] = response.get('is_admin', False)
                    settings['activate_hwid'] = App._act_hwid
                    history = settings.get('activate_keys', [])
                    names = [item.get('key', '') if isinstance(item, dict) else item for item in history]
                    if key not in names:
                        history.append({'key': key, 'name': name or '未命名'})
                    settings['activate_keys'] = history
                    save_settings(settings)
                    _kc_wcache(App._act_cache, response, key, App._act_hwid)
                    return (True, '', response)
                last_error = response.get('reason', '验证失败') if 'ok' in response else '无法连接激活服务器'
            except Exception as exc:
                last_error = str(exc) if 'Errno' in str(exc) else '无法连接激活服务器'
        return (False, last_error, {})

    @staticmethod
    def _show_activate_dialog():
        dialog = tk.Toplevel()
        dialog.title('激活验证')
        dialog.attributes('-topmost', True)
        dialog.geometry('500x360')
        dialog.resizable(False, False)
        tk.Label(dialog, text='用户名（首次激活填写）', font=('Microsoft YaHei UI', 10)).pack(pady=(24, 5))
        name_var = tk.StringVar()
        tk.Entry(dialog, textvariable=name_var, width=28, justify='center').pack()
        tk.Label(dialog, text='输入激活码', font=('Microsoft YaHei UI', 10)).pack(pady=(18, 5))
        key_var = tk.StringVar(value=App._act_key)
        tk.Entry(dialog, textvariable=key_var, width=36, justify='center', font=('Consolas', 11)).pack()
        result = [False]
        status = tk.Label(dialog, text='', fg='#ef4444')
        status.pack(pady=8)

        def submit():
            key = key_var.get().strip()
            if not key:
                status.config(text='请输入激活码')
                return
            ok, reason, _ = App._online_verify_silent(key, name_var.get().strip())
            if ok:
                result[0] = True
                dialog.destroy()
            else:
                status.config(text=reason)
        bar = tk.Frame(dialog)
        bar.pack(pady=12)
        tk.Button(bar, text='确定激活', command=submit, bg='#238636', fg='white', padx=18, pady=6).pack(side='left', padx=5)
        tk.Button(bar, text='获取激活码', command=lambda: webbrowser.open('http://47.79.117.138:5888/trial'), bg='#E91E63', fg='white', padx=18, pady=6).pack(side='left', padx=5)
        dialog.grab_set()
        dialog.wait_window()
        return result[0]
    _act_dialog_func = _show_activate_dialog

    @staticmethod
    def _heartbeat():
        time.sleep(5)
        while True:
            time.sleep(300)
            if not App._act_key:
                continue
            payload = json.dumps({'key': App._act_key, 'hwid': App._act_hwid}).encode()
            for server in App._act_srv_list:
                if not server:
                    continue
                try:
                    request = urllib.request.Request(f'{server}/ping', data=payload, headers={'Content-Type': 'application/json'})
                    response = json.loads(urllib.request.urlopen(request, timeout=3).read())
                    if response.get('ok') and _kc_verify(response, App._act_key, App._act_hwid):
                        if response.get('type'):
                            App._act_type = response['type']
                        if response.get('expires'):
                            App._act_exp = response['expires']
                        settings = load_settings()
                        settings['activate_type'] = App._act_type
                        settings['activate_exp'] = App._act_exp
                        save_settings(settings)
                        _kc_wcache(App._act_cache, response, App._act_key, App._act_hwid)
                    break
                except Exception:
                    continue

    @staticmethod
    def _send_telemetry(event, script='', error='', duration=0):

        def worker():
            payload = json.dumps({'key': App._act_key, 'hwid': App._act_hwid, 'event': event, 'script': script, 'error': error, 'duration': duration, 'version': 'v26.8.21'}).encode()
            for server in App._act_srv_list:
                if not server:
                    continue
                try:
                    request = urllib.request.Request(f'{server}/telemetry', data=payload, headers={'Content-Type': 'application/json'})
                    urllib.request.urlopen(request, timeout=3)
                    return
                except Exception:
                    continue
        threading.Thread(target=worker, daemon=True).start()

    def _bind_warn_start(self):
        if getattr(self, '_bind_warn_on', False):
            return None
        self._bind_warn_on = True
        self._bind_warn_red = False
        self._bind_warn_tick()
        return None

    def _bind_warn_stop(self):
        if not getattr(self, '_bind_warn_on', False):
            return None
        self._bind_warn_on = False
        try:
            if getattr(self, '_bind_btn', None):
                self._bind_btn.configure(bg=POP_BTN)
        except Exception:
            pass
        return None

    def _bind_warn_tick(self):
        if not getattr(self, '_bind_warn_on', False):
            return None
        _b = getattr(self, '_bind_btn', None)
        if _b is None:
            return None
        if self._bind_warn_red:
            _b.configure(bg='#ef4444')
            self._bind_warn_red = not self._bind_warn_red
        else:
            _b.configure(bg='#dc2626')
            self._bind_warn_red = not self._bind_warn_red
        self.root.after(500, self._bind_warn_tick)
        return None

    def _update_bind_title(self, text):
        if not text:
            self._bind_full = '请绑定窗口方可正常使用'
        else:
            self._bind_full = text
        if len(self._bind_full) <= 23:
            self._bind_title.set(self._bind_full)
            return None
        self._bind_title.set(self._bind_full[slice(None, 11)] + '…' + self._bind_full[slice(-11, None)])
        return None

    def _bind_tip_show(self, _event=None):
        try:
            if len(self._bind_full) <= 23 or hasattr(self, '_bind_tip_win'):
                return None
            self._bind_tip_win = tk.Toplevel(self.root)
            self._bind_tip_win.overrideredirect(True)
            self._bind_tip_win.attributes('-topmost', True)
            tk.Label(self._bind_tip_win, text=self._bind_full, bg=POP_CARD, fg='#e6edf3', font=('Microsoft YaHei UI', 9), padx=8, pady=4).pack()
            self._bind_tip_pos()
        except Exception:
            pass
        return None

    def _bind_tip_pos(self):
        try:
            self._bind_tip_win.geometry('+%d+%d' % (self.root.winfo_pointerx() + 14, self.root.winfo_pointery() + 14))
        except Exception:
            pass

    def _bind_tip_hide(self, _event=None):
        try:
            self._bind_tip_win.destroy()
            del self._bind_tip_win
        except Exception:
            pass

    def _open_driver_helper(self):
        current = getattr(self, '_helper_win', None)
        if current and current.winfo_exists():
            current.lift()
            current.focus_force()
            return
        window = tk.Toplevel(self.root)
        self._helper_win = window
        window.title('驱动助手')
        window.geometry('680x401')
        window.configure(bg=POP_BG)
        window.resizable(False, False)
        window.transient(self.root)
        try:
            window.attributes('-topmost', True)
            if self._icon_path:
                window.iconbitmap(default=self._icon_path)
        except Exception:
            pass
        tk.Label(window, text='驱动助手', bg=POP_BG, fg='#e6edf3', font=('Microsoft YaHei UI', 14, 'bold')).pack(pady=(12, 2))
        tk.Label(window, text='点击卡片选择驱动(重启软件后生效) · 推荐 VIIPER: 免内核最稳', bg=POP_BG, fg=POP_SUB, font=('Microsoft YaHei UI', 9)).pack()
        names = {'viiper': 'VIIPER', 'ttinput': 'KE Driver', 'fakerinput': 'FakerInput'}
        descriptions = {'viiper': '推荐 · 虚拟HID(免内核,最稳)', 'ttinput': '内核驱动(专业级,WHQL签名)', 'fakerinput': '备用虚拟HID(兼容旧机)'}
        colors = {'viiper': '#2dd4bf', 'ttinput': '#10b981', 'fakerinput': '#e879f9'}
        cards = {}
        selected = {}
        for mode in ('viiper', 'ttinput', 'fakerinput'):
            row = tk.Frame(window, bg=POP_CARD, width=648, height=62)
            row.pack(fill='x', padx=16, pady=4)
            row.pack_propagate(False)
            variable = tk.BooleanVar(value=mode == self._driver_mode)
            selected[mode] = variable
            checkbox = tk.Checkbutton(row, variable=variable, command=lambda value=mode: self._helper_select(value, cards, selected, selected), font=('Microsoft YaHei UI', 12, 'bold'), bg=POP_CARD, fg='#3fb950', activebackground=POP_CARD, selectcolor=POP_CARD, bd=0)
            checkbox.pack(side='left', padx=(8, 0), pady=8)
            name_label = tk.Label(row, text=names[mode], bg=POP_CARD, fg=colors[mode], font=('Microsoft YaHei UI', 11, 'bold'), width=10, anchor='w', cursor='hand2')
            name_label.pack(side='left', padx=(0, 4), pady=8)
            description = tk.Label(row, text=descriptions[mode], bg=POP_CARD, fg=POP_SUB, font=('Microsoft YaHei UI', 8), anchor='w', cursor='hand2')
            description.pack(side='left', pady=8)
            status = tk.Label(row, text='检测中', bg=POP_CARD, fg='#f59e0b', font=('Microsoft YaHei UI', 9, 'bold'), width=7)
            status.pack(side='right', padx=4, pady=8)
            operations = tk.Frame(row, bg=POP_CARD)
            operations.pack(side='right', pady=8)
            tk.Button(operations, text='删除', command=lambda value=mode: self._helper_uninstall(value, cards), font=('Microsoft YaHei UI', 9), bg='#da3633', fg='white', relief='flat', padx=10, pady=2).pack(side='left', padx=2)
            tk.Button(operations, text='安装', command=lambda value=mode: self._helper_install(value, cards), font=('Microsoft YaHei UI', 9, 'bold'), bg='#238636', fg='white', relief='flat', padx=10, pady=2).pack(side='left', padx=2)
            for widget in (row, name_label, description):
                widget.bind('<Button-1>', lambda _event, value=mode: self._helper_select(value, cards, selected, selected))
            cards[mode] = {'row': row, 'status': status, 'var': variable, 'name': names[mode]}
        controls = tk.Frame(window, bg=POP_BG)
        controls.pack(fill='x', padx=16, pady=(8, 4))
        tk.Button(controls, text='一键全部安装', command=lambda: self._install_all(cards), bg=POP_BTN, fg=POP_BTN_FG, relief='flat', font=('Microsoft YaHei UI', 10, 'bold'), padx=14, pady=4).pack(side='left', padx=4)
        tk.Button(controls, text='一键全部删除', command=lambda: self._uninstall_all(cards), bg=POP_BTN, fg=POP_BTN_FG, relief='flat', font=('Microsoft YaHei UI', 10), padx=14, pady=4).pack(side='left', padx=4)
        tk.Button(controls, text='刷新状态', command=lambda: self._helper_refresh(cards), bg=POP_BTN, fg=POP_TXT, relief='flat', font=('Microsoft YaHei UI', 10), padx=10, pady=4).pack(side='left', padx=4)
        tk.Label(window, text='安装/删除需要管理员权限, 弹出授权框请点“是”', bg=POP_BG, fg=POP_SUB, font=('Microsoft YaHei UI', 8)).pack(pady=(2, 10))

        def close():
            self._helper_win = None
            window.destroy()

        window.protocol('WM_DELETE_WINDOW', close)
        window.update_idletasks()
        window.geometry(f'+{max(0, self.root.winfo_x() + (self.root.winfo_width() - window.winfo_width()) // 2)}+{max(0, self.root.winfo_y() + (self.root.winfo_height() - window.winfo_height()) // 2)}')
        self._helper_refresh(cards)

    def _helper_refresh(self, cards=None):
        cards = cards or getattr(self, '_helper_cards', None)
        if cards is None:
            return
        self._helper_cards = cards

        def work():
            states = {}
            for mode in ('viiper', 'ttinput', 'fakerinput'):
                try:
                    self._drv_inst_cache.pop(mode, None)
                    states[mode] = self._driver_installed(mode)
                except Exception as exc:
                    states[mode] = False
                    self._log(f'[驱动助手] {mode} 状态检测失败: {exc}')
            self._safe_after(0, self._refresh_done, states, cards)

        threading.Thread(target=work, daemon=True, name='driver_helper_refresh').start()

    def _refresh_done(self, states, cards=None):
        cards = cards or getattr(self, '_helper_cards', {})
        for mode, installed in states.items():
            card = cards.get(mode)
            if not card:
                continue
            card['status'].configure(text='已安装' if installed else '未安装', fg='#3fb950' if installed else '#f85149')
            card['var'].set(mode == self._driver_mode)
        self._refresh_driver_ui()

    def _install_all(self, cards=None):
        cards = cards or getattr(self, '_helper_cards', {})
        for delay, mode in enumerate(('viiper', 'ttinput', 'fakerinput')):
            self.root.after(delay * 500, lambda value=mode: self._helper_install(value, cards))

    def _helper_install(self, mode, cards=None):
        cards = cards or getattr(self, '_helper_cards', {})
        if self._helper_op.get(mode):
            return
        self._helper_op[mode] = True
        name = {'viiper': 'VIIPER', 'ttinput': 'KE Driver', 'fakerinput': 'FakerInput'}.get(mode, mode)
        if mode in cards:
            cards[mode]['status'].configure(text='安装中', fg='#f59e0b')

        def work():
            try:
                if mode == 'viiper':
                    result = self._ensure_viiper()
                elif mode == 'fakerinput':
                    result = self._ensure_faker()
                else:
                    result = self._ensure_ttinput()
            except Exception as exc:
                self._log(f'[驱动助手] {name} 安装异常: {exc}')
                result = False
            self._safe_after(0, self._helper_install_done, mode, result, cards, name)

        threading.Thread(target=work, daemon=True, name=f'driver_install_{mode}').start()

    def _ensure_ttinput(self):
        if self._driver_installed('ttinput'):
            return 'ok'
        driver_dir = getattr(sys, '_MEIPASS', None) or SCRIPT_DIR
        devcon = os.path.join(driver_dir, 'devcon.exe')
        inf = os.path.join(driver_dir, 'ttinput.inf')
        sys_file = os.path.join(driver_dir, 'ttinput.sys')
        if not all(os.path.isfile(path) for path in (devcon, inf, sys_file)):
            return 'nofile'
        command = f'/c ""{devcon}" remove ROOT\\ttinput* >nul 2>&1 & sc stop ttinputhid >nul 2>&1 & sc delete ttinputhid >nul 2>&1 & "{devcon}" install "{inf}" ROOT\\ttinput"'
        result = ctypes.windll.shell32.ShellExecuteW(None, 'runas', 'cmd.exe', command, driver_dir, 0)
        return 'install' if result > 32 else 'cancel'

    def _ensure_faker(self):
        if self._driver_installed('fakerinput'):
            return 'ok'
        driver_dir = getattr(sys, '_MEIPASS', None) or SCRIPT_DIR
        devcon = os.path.join(driver_dir, 'devcon.exe')
        faker_dir = os.path.join(driver_dir, 'FakerInput')
        inf = os.path.join(faker_dir, 'fakerinput.inf')
        dll = os.path.join(faker_dir, 'FakerInput.dll')
        if not all(os.path.isfile(path) for path in (devcon, inf, dll)):
            return 'nofile'
        command = f'/c ""{devcon}" remove ROOT\\FakerInput >nul 2>&1 & "{devcon}" install "{inf}" ROOT\\FakerInput"'
        result = ctypes.windll.shell32.ShellExecuteW(None, 'runas', 'cmd.exe', command, faker_dir, 0)
        return 'install' if result > 32 else 'cancel'

    def _faker_restart_wait(self):
        for _ in range(20):
            time.sleep(0.25)
            self._drv_inst_cache.pop('fakerinput', None)
            if self._driver_installed('fakerinput'):
                return True
        return False

    def _ensure_viiper(self):
        if self._driver_installed('viiper'):
            return True
        runtime_dir = getattr(sys, '_MEIPASS', None) or SCRIPT_DIR
        daemon = os.path.join(runtime_dir, 'VIIPER', 'viiper.exe')
        installer = os.path.join(runtime_dir, 'USBip-0.9.7.7-x64-release.exe')
        usbip = r'C:\Program Files\USBip\usbip.exe'
        if not os.path.isfile(usbip):
            if not os.path.isfile(installer):
                self._log('[VIIPER] usbip-win2 安装包缺失')
                return False
            result = ctypes.windll.shell32.ShellExecuteW(None, 'runas', installer, '', runtime_dir, 0)
            return 'installing' if result > 32 else False
        if not os.path.isfile(daemon):
            self._log('[VIIPER] 守护程序缺失: ' + daemon)
            return False
        try:
            subprocess = __import__('subprocess')
            subprocess.Popen([daemon], cwd=os.path.dirname(daemon), stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, creationflags=getattr(subprocess, 'CREATE_NO_WINDOW', 0))
        except Exception as exc:
            self._log(f'[VIIPER] 守护程序启动失败: {exc}')
            return False
        for _ in range(20):
            time.sleep(0.25)
            self._drv_inst_cache.pop('viiper', None)
            if self._driver_installed('viiper'):
                return True
        self._log('[VIIPER] 守护程序未在规定时间内就绪')
        return False

    def _uninstall_all(self, cards=None):
        if not messagebox.askyesno('驱动删除', '确定删除全部三种驱动？\n\n操作需要管理员权限。', parent=getattr(self, '_helper_win', self.root)):
            return
        cards = cards or getattr(self, '_helper_cards', {})
        threading.Thread(target=self._uninstall_all_work, args=(cards,), daemon=True, name='driver_uninstall_all').start()

    def _uninstall_all_work(self, cards=None):
        results = {}
        for mode in ('viiper', 'ttinput', 'fakerinput'):
            results[mode] = self._uninstall_driver(mode)
        self._safe_after(0, self._uninstall_all_done, results, cards or {})

    def _uninstall_all_done(self, results, cards=None):
        self._helper_refresh(cards)
        if all(results.values()):
            self._alert('驱动删除', '全部删除命令已提交，请稍后刷新状态')
        else:
            self._alert('驱动删除', '部分删除命令未能提交，请查看日志')

    def _uninstall_all_verify(self, cards=None):
        self._helper_refresh(cards)

    def _helper_uninstall(self, mode, cards=None):
        name = {'viiper': 'VIIPER', 'ttinput': 'KE Driver', 'fakerinput': 'FakerInput'}.get(mode, mode)
        if not messagebox.askyesno('驱动删除', f'确定删除 {name}？', parent=getattr(self, '_helper_win', self.root)):
            return
        if self._helper_op.get(mode):
            return
        self._helper_op[mode] = True

        def work():
            result = self._uninstall_driver(mode)
            self._safe_after(0, self._helper_uninstall_done, mode, result, cards or {}, name)

        threading.Thread(target=work, daemon=True, name=f'driver_uninstall_{mode}').start()

    def _uninstall_driver(self, mode):
        driver_dir = getattr(sys, '_MEIPASS', None) or SCRIPT_DIR
        devcon = os.path.join(driver_dir, 'devcon.exe')
        try:
            if mode == 'viiper':
                self._viper_unload()
                return True
            if not os.path.isfile(devcon):
                self._log('[驱动助手] devcon.exe 缺失')
                return False
            if mode == 'ttinput':
                command = f'/c ""{devcon}" remove ROOT\\ttinput* & sc stop ttinputhid & sc delete ttinputhid"'
            else:
                command = f'/c ""{devcon}" remove ROOT\\FakerInput"'
            result = ctypes.windll.shell32.ShellExecuteW(None, 'runas', 'cmd.exe', command, driver_dir, 0)
            return result > 32
        except Exception as exc:
            self._log(f'[驱动助手] 删除 {mode} 失败: {exc}')
            return False

    def _helper_uninstall_done(self, mode, result, cards, name):
        self._helper_op[mode] = False
        self._drv_inst_cache.pop(mode, None)
        self._helper_refresh(cards)
        self._float_blink(f'{name} 删除命令已提交' if result else f'{name} 删除失败', '#3fb950' if result else '#f85149')

    def _helper_verify_deleted(self, mode, cards=None):
        self._drv_inst_cache.pop(mode, None)
        deleted = not self._driver_installed(mode)
        self._helper_refresh(cards)
        return deleted

    def _driver_installed(self, mode):
        now = time.time()
        cached = self._drv_inst_cache.get(mode)
        if cached and now - cached[0] < 10:
            return cached[1]
        installed = False
        try:
            if mode == 'viiper':
                if os.path.isfile(r'C:\\Program Files\\USBip\\usbip.exe'):
                    try:
                        connection = socket.create_connection(('127.0.0.1', ViiperInput._API_PORT), timeout=0.5)
                        connection.close()
                        api_up = True
                    except OSError:
                        api_up = False
                    try:
                        service_state, _malformed = _viper_l2_ude()
                    except Exception:
                        service_state = 0
                    installed = service_state > 0 if service_state else api_up
            elif mode == 'ttinput':
                subprocess = __import__('subprocess')
                result = subprocess.run(['sc.exe', 'query', 'ttinputhid'], capture_output=True, text=True, encoding='gbk', errors='replace', creationflags=getattr(subprocess, 'CREATE_NO_WINDOW', 0), timeout=5)
                if 'RUNNING' in result.stdout:
                    driver_dir = getattr(sys, '_MEIPASS', None) or SCRIPT_DIR
                    devcon = os.path.join(driver_dir, 'devcon.exe')
                    if not os.path.isfile(devcon):
                        devcon = os.path.join(SCRIPT_DIR, 'devcon.exe')
                    if os.path.isfile(devcon):
                        device = subprocess.run([devcon, 'findall', 'ROOT\\ttinput*'], capture_output=True, text=True, encoding='gbk', errors='replace', creationflags=getattr(subprocess, 'CREATE_NO_WINDOW', 0), timeout=10)
                        installed = 'ROOT' in device.stdout.upper()
                    else:
                        installed = True
            elif mode == 'fakerinput':
                installed = FakerInputInput.find_col05() is not None
                if installed:
                    subprocess = __import__('subprocess')
                    driver_dir = getattr(sys, '_MEIPASS', None) or SCRIPT_DIR
                    devcon = os.path.join(driver_dir, 'devcon.exe')
                    if os.path.isfile(devcon):
                        device = subprocess.run([devcon, 'findall', 'ROOT\\FakerInput'], capture_output=True, text=True, encoding='gbk', errors='replace', creationflags=getattr(subprocess, 'CREATE_NO_WINDOW', 0), timeout=10)
                        installed = 'ROOT\\SYSTEM' in device.stdout.upper() or 'ROOT\\FAKERINPUT' in device.stdout.upper()
        except Exception as exc:
            installed = False
            self._log(f'[驱动助手] {mode} 状态检测异常: {exc}')
        self._drv_inst_cache[mode] = (time.time(), bool(installed))
        return bool(installed)

    def _helper_install_done(self, mode, _rc, cards, _nm):
        self._helper_op[mode] = False
        self._helper_refresh(cards)
        if mode == 'viiper':
            if _rc is True:
                self._float_blink('VIIPER 已就绪', '#3fb950')
                return None
            if _rc == 'installing':
                self._alert('驱动安装', 'usbip-win2 正在静默安装(需管理员)\n\n完成后重启软件生效')
                return None
            self._log('[驱动助手] VIIPER 安装指引: 查看上方日志中 [VIIPER] 条目定位原因')
            self._alert('驱动安装', 'VIIPER 未就绪\n    \n    原因分类(见日志 [VIIPER] 条目):\n    • 守护缺失 → 检查打包资源驱动/VIIPER/viiper.exe\n    • 守护拉起失败 → 重启电脑后重试\n    • usbip-win2 安装包缺失 → 请切换回 KE Driver')
            return None
        if mode == 'ttinput':
            if _rc == 'ok':
                self._float_blink('KE Driver 已就绪', '#3fb950')
                return None
            if _rc == 'blocked':
                self._alert('驱动安装', 'KE Driver 服务清理中(NOT_STOPPABLE)\n\n重启电脑后服务消失, 再点"安装"即可装回')
                return None
            if _rc == 'install':
                self._alert('驱动安装', 'KE Driver 安装已发起(静默), 稍后自动生效')
                return None
            if _rc == 'cancel':
                self._float_blink('KE Driver 安装被取消(需要管理员权限)', '#f85149')
                return None
            if _rc == 'nofile':
                self._alert('驱动安装', 'KE Driver 驱动文件不齐(inf/sys/devcon), 请重新安装软件')
                return None
            self._float_blink('KE Driver 未就绪, 详见日志', '#f85149')
            return None
        if _rc == 'ok':
            self._alert('驱动安装', 'FakerInput 已就绪\n\n重启软件后生效\n（引擎启动时才加载该驱动）')
            return None
        if _rc == 'install':
            self._alert('驱动安装', 'FakerInput 安装已发起(静默)\n\n完成后重启软件生效')
            return None
        if _rc == 'cancel':
            self._float_blink('FakerInput 安装被取消(需要管理员权限)', '#f85149')
            return None
        if _rc == 'nofile':
            self._alert('驱动安装', 'FakerInput 驱动文件不齐(inf/dll/devcon), 请重新安装软件')
            return None
        self._float_blink('FakerInput 未就绪, 详见日志', '#f85149')
        return None

    def _helper_select(self, mode, cards, sels, sel_vars):
        if mode == self._driver_mode:
            sel_vars[mode].set(True)
            return None
        _nm = {'viiper': 'VIIPER', 'ttinput': 'KE Driver', 'fakerinput': 'FakerInput'}.get(mode, mode)
        if not self._driver_installed(mode):
            sel_vars[mode].set(False)
            self._float_blink('%s 未安装, 先点该卡片右侧"安装"' % _nm, '#f85149')
            return None
        self._driver_mode = mode
        self.settings['input_mode'] = mode
        save_settings(self.settings)
        self._refresh_driver_ui()
        for _m, _v in sel_vars.items():
            _v.set(_m == mode)
        self._log('[驱动助手] 已选择驱动 →' + str(_nm))
        self._float_blink('已选择 %s, 重启软件后生效' % _nm, '#f59e0b')
        return None

    def _viper_unload(self):
        import socket as socket_module
        import subprocess as subprocess_module
        had_daemon = False
        try:
            connection = socket_module.create_connection(
                ('127.0.0.1', ViiperInput._API_PORT), timeout=0.5
            )
            connection.close()
            had_daemon = True
        except OSError:
            pass
        if had_daemon:
            try:
                viiper = ViiperInput.__new__(ViiperInput)
                viiper._pw = ViiperInput._read_password()
                viiper._sock_kb = None
                viiper._sock_ms = None
                viiper._cleanup()
            except Exception as exc:
                self._log(f'[驱动助手] VIIPER 摘设备异常: {exc}')
        try:
            subprocess_module.run(
                ['taskkill', '/f', '/im', 'viiper.exe'],
                capture_output=True,
                timeout=5,
                creationflags=0x08000000,
            )
        except Exception:
            pass
        return had_daemon

    def _ude_children(self, rel_out):
        children = []
        in_children = False
        for line in rel_out.splitlines():
            value = line.rstrip()
            lowered = value.lower()
            if (
                lowered.startswith('children:')
                or lowered.startswith('子设备:')
                or lowered.startswith('子设备：')
            ):
                in_children = True
                separator = ':' if ':' in value else '：'
                tail = value.split(separator, 1)[1].strip()
                if not tail:
                    continue
                value = tail
            elif in_children and (value.startswith(' ') or value.startswith('\t')):
                pass
            else:
                in_children = False
                continue
            token = value.split()[0] if value.strip() else ''
            if token.upper().startswith('HID\\') and '&' in token and token not in children:
                children.append(token)
        return children

    def _viper_ude_ids(self):
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
            return []
        devices = []
        current = ''
        for line in output.splitlines():
            value = line.strip()
            lowered = value.lower()
            if lowered.startswith('instance id:') or lowered.startswith('实例 id:'):
                current = value.split(':', 1)[1].strip()
                continue
            if (
                lowered.startswith('driver name:')
                or lowered.startswith('驱动程序名称:')
            ) and 'usbip' in lowered and current.lower().startswith('root\\usb'):
                devices.append(current)
        return devices

    def _verify_launch_cont(self):
        if self.runner:
            self.runner.stop()
            self.runner = None
        self.status_text.config(text='驱动加载中(首次约2~4秒)…')
        self.root.update_idletasks()
        self._launch_runner()
        return None

def _single_instance_check():
    try:
        mutex = ctypes.windll.kernel32.CreateMutexW(None, False, 'KEDriver_SingleInstance_Mutex')
        if ctypes.windll.kernel32.GetLastError() == 183:
            ctypes.windll.user32.MessageBoxW(0, 'K3M2已在运行中', '提示', 64)
            return False
        globals()['_APP_MUTEX'] = mutex
    except Exception:
        pass
    try:
        import subprocess
        output = subprocess.run(
            ['tasklist', '/FI', 'IMAGENAME eq KE外设.exe', '/FO', 'CSV', '/NH'],
            capture_output=True,
            text=True,
            encoding='gbk',
            errors='replace',
            timeout=10,
            creationflags=0x08000000,
        ).stdout
        if any('KE外设.exe' in line for line in output.splitlines()):
            ctypes.windll.user32.MessageBoxW(
                0,
                '检测到旧版本实例仍在运行(新旧并存会导致启停热键冲突失效)。\n'
                '请先在任务管理器结束旧版 KE外设.exe, 再重新启动本版本。',
                '提示',
                48,
            )
            return False
    except Exception:
        pass
    return True
if __name__ == '__main__':
    if '--selfcheck' in sys.argv:
        from ke_sentinel import run_selfcheck_only
        run_selfcheck_only()
    try:
        console = ctypes.windll.kernel32.GetConsoleWindow()
        if console:
            ctypes.windll.user32.ShowWindow(console, 0)
    except Exception:
        pass
    if _single_instance_check():
        threading.Thread(target=warm_tts, daemon=True).start()
        threading.Thread(target=App._heartbeat, daemon=True).start()
        App().run()
