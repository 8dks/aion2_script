import base64
import hashlib
import json
import os
import sys
import threading
import time


_ED_PUB_DER = bytes.fromhex(
    '302a300506032b6570032100e1b8cd22670b5f14e32381fb9852d74dc85129503ea224b29cb0d159eaff657e'
)
_ED_PUB = None
_act_key = ''
_act_hwid = ''
_act_type = ''
_act_exp = ''
_act_ok = False


def _ed_pub():
    global _ED_PUB
    if _ED_PUB is None:
        from cryptography.hazmat.primitives import serialization
        _ED_PUB = serialization.load_der_public_key(_ED_PUB_DER)
    return _ED_PUB


def verify_resp(resp, key, hwid):
    try:
        if not resp or not resp.get('sig') or not resp.get('server_ts'):
            return False
        is_admin = '1' if resp.get('is_admin') else ''
        payload = '1|%s|%s|%s|%s|%s|%s' % (
            resp.get('type', ''),
            resp.get('expires', ''),
            is_admin,
            key,
            hwid,
            resp.get('server_ts'),
        )
        _ed_pub().verify(base64.b64decode(resp['sig']), payload.encode())
        return True
    except Exception:
        return False


def write_act_cache(cache_file, resp, key, hwid):
    try:
        is_admin = '1' if resp.get('is_admin') else ''
        payload = '1|%s|%s|%s|%s|%s|%s' % (
            resp.get('type', ''),
            resp.get('expires', ''),
            is_admin,
            key,
            hwid,
            resp.get('server_ts'),
        )
        temporary = cache_file + '.tmp'
        with open(temporary, 'w', encoding='utf-8') as stream:
            stream.write('V2\n%s\n%s' % (payload, resp.get('sig', '')))
        os.replace(temporary, cache_file)
        return True
    except Exception:
        return False


def read_act_cache(cache_file, key, hwid):
    try:
        with open(cache_file, 'r', encoding='utf-8') as stream:
            raw = stream.read().strip()
        parts = raw.split('\n')
        if len(parts) != 3 or parts[0] != 'V2':
            return None
        payload, signature = parts[1], parts[2]
        _ed_pub().verify(base64.b64decode(signature), payload.encode())
        fields = payload.split('|')
        if len(fields) != 7 or fields[0] != '1':
            return None
        activation_type, expires, is_admin, cached_key, cached_hwid, server_ts = fields[1:]
        if cached_key != key or cached_hwid != hwid:
            return None
        if len(server_ts) == 10 and int(server_ts) < int(time.time()) - 604800:
            return None
        return activation_type, expires, is_admin == '1'
    except Exception:
        return None


def init_activation(_settings=None):
    from DD import SCRIPT_DIR, SCRIPTS_DIR, SETTINGS_FILE, load_settings, save_settings
    import socket
    import uuid as _uuid
    from ke_engine import legacy_hwid, stable_hwid

    del SETTINGS_FILE, SCRIPTS_DIR, socket
    global _act_key, _act_hwid, _act_type, _act_exp, _act_ok
    servers = ['http://47.79.117.138:5888']
    _act_key = load_settings().get('activate_key', '')
    _act_ok = False
    _act_type = ''
    _act_exp = ''
    _act_hwid = stable_hwid()
    cache_file = os.path.join(SCRIPT_DIR, '激活缓存')

    def save_response(response):
        global _act_type, _act_exp
        _act_type = response.get('type', '')
        _act_exp = response.get('expires', '')
        settings = load_settings()
        settings['activate_key'] = _act_key
        settings['activate_type'] = _act_type
        settings['activate_exp'] = _act_exp
        settings['is_admin'] = response.get('is_admin', False)
        save_settings(settings)
        if _settings is not None:
            keys = ('activate_key', 'activate_type', 'activate_exp', 'is_admin')
            _settings.update({name: settings[name] for name in keys if name in settings})
        write_act_cache(cache_file, response, _act_key, _act_hwid)

    if _act_key:
        cached = read_act_cache(cache_file, _act_key, _act_hwid)
        if cached:
            _act_ok = True
            _act_type, _act_exp, _act_is_admin = cached
        if not _act_ok:
            try:
                import urllib.request as request
                payload = json.dumps(
                    {'key': _act_key, 'hwid': _act_hwid, 'legacy_hwid': legacy_hwid()}
                ).encode()
                response = None
                for server in servers:
                    if not server:
                        continue
                    try:
                        query = request.Request(
                            f'{server}/verify',
                            data=payload,
                            headers={'Content-Type': 'application/json'},
                        )
                        response = json.loads(request.urlopen(query, timeout=3).read())
                        break
                    except Exception:
                        continue
                if response and response.get('ok') and verify_resp(response, _act_key, _act_hwid):
                    _act_ok = True
                    save_response(response)
            except Exception:
                pass

    if _act_key and not _act_ok:
        try:
            import urllib.request as request
            payload = json.dumps(
                {'key': _act_key, 'hwid': _act_hwid, 'legacy_hwid': legacy_hwid()}
            ).encode()
            for server in servers:
                try:
                    query = request.Request(
                        f'{server}/verify',
                        data=payload,
                        headers={'Content-Type': 'application/json'},
                    )
                    response = json.loads(request.urlopen(query, timeout=3).read())
                    if response and response.get('ok') and verify_resp(response, _act_key, _act_hwid):
                        _act_ok = True
                        save_response(response)
                        break
                except Exception:
                    continue
        except Exception:
            pass

    def show_activate_dialog():
        global _act_key, _act_ok, _act_type, _act_exp
        import tkinter as tk

        dialog = tk.Tk()
        dialog.title('激活验证')
        dialog.configure(bg='#1a1a2e')
        try:
            directories = (
                [getattr(sys, '_MEIPASS', None), SCRIPT_DIR]
                if getattr(sys, '_MEIPASS', None)
                else [SCRIPT_DIR]
            )
            for directory in directories:
                if not directory:
                    continue
                for filename in ('icon_main.ico', 'icon_pink.ico'):
                    icon_path = os.path.join(directory, filename)
                    if os.path.isfile(icon_path):
                        dialog.iconbitmap(icon_path)
                        raise StopIteration
        except StopIteration:
            pass
        except Exception:
            pass
        dialog.geometry(
            '400x320+%d+%d'
            % (dialog.winfo_screenwidth() // 2 - 200, dialog.winfo_screenheight() // 2 - 160)
        )
        dialog.resizable(False, False)
        tk.Label(
            dialog,
            text='用户名(首次激活填写)',
            font=('Microsoft YaHei UI', 10),
            fg='#8b949e',
            bg='#1a1a2e',
        ).pack(pady=(20, 4))
        name_entry = tk.Entry(
            dialog,
            font=('Microsoft YaHei UI', 11),
            width=20,
            bg='#0d1117',
            fg='#c9d1d9',
            insertbackground='#58a6ff',
            relief='flat',
            justify='center',
        )
        name_entry.pack(pady=4)
        name_entry.focus_set()
        tk.Label(
            dialog,
            text='输入激活码',
            font=('Microsoft YaHei UI', 10),
            fg='#8b949e',
            bg='#1a1a2e',
        ).pack(pady=(12, 4))
        key_entry = tk.Entry(
            dialog,
            font=('Consolas', 12),
            width=28,
            bg='#0d1117',
            fg='#58a6ff',
            insertbackground='#58a6ff',
            relief='flat',
            justify='center',
        )
        key_entry.pack(pady=4)
        key_entry.bind('<Return>', lambda _event: dialog.quit())

        def quick_trial():
            try:
                import urllib.request as request
                from ke_engine import legacy_hwid as current_legacy_hwid
                from ke_engine import stable_hwid as current_hwid
                payload = json.dumps(
                    {'hwid': current_hwid(), 'legacy_hwid': current_legacy_hwid()}
                ).encode()
                query = request.Request(
                    f'{servers[0]}/quick_trial',
                    data=payload,
                    headers={'Content-Type': 'application/json'},
                    method='POST',
                )
                response = json.loads(request.urlopen(query, timeout=3).read())
                if response.get('key'):
                    key_entry.delete(0, 'end')
                    key_entry.insert(0, response['key'])
                    dialog.quit()
                else:
                    tk.messagebox.showerror('错误', response.get('error', '获取失败'))
            except Exception:
                tk.messagebox.showerror('错误', '网络错误')

        button_frame = tk.Frame(dialog, bg='#1a1a2e')
        button_frame.pack(pady=(40, 16))
        tk.Button(
            button_frame,
            text='立即试用',
            font=('Microsoft YaHei UI', 10),
            bg='#1f6feb',
            fg='white',
            relief='flat',
            padx=14,
            pady=6,
            cursor='hand2',
            command=quick_trial,
        ).pack(side='left', padx=4)
        tk.Button(
            button_frame,
            text='确定激活',
            font=('Microsoft YaHei UI', 10, 'bold'),
            bg='#238636',
            fg='white',
            relief='flat',
            padx=18,
            pady=6,
            cursor='hand2',
            command=dialog.quit,
        ).pack(side='left', padx=4)
        dialog.mainloop()
        entered_key = key_entry.get().strip()
        entered_name = name_entry.get().strip()
        try:
            dialog.destroy()
        except Exception:
            pass
        if not entered_key:
            return False
        try:
            import urllib.error as url_error
            import urllib.request as request
            from ke_engine import legacy_hwid as current_legacy_hwid
            from ke_engine import stable_hwid as current_hwid
            payload = json.dumps(
                {
                    'key': entered_key,
                    'hwid': current_hwid(),
                    'legacy_hwid': current_legacy_hwid(),
                    'name': entered_name,
                }
            ).encode()
            for server in servers:
                try:
                    query = request.Request(
                        f'{server}/verify',
                        data=payload,
                        headers={'Content-Type': 'application/json'},
                    )
                    response = json.loads(request.urlopen(query, timeout=3).read())
                    if response.get('ok') and verify_resp(response, entered_key, _act_hwid):
                        _act_ok = True
                        _act_key = entered_key
                        save_response(response)
                        return True
                    tk.messagebox.showerror('激活失败', response.get('reason', '验证失败'))
                    return False
                except url_error.HTTPError as http_error:
                    try:
                        raw = http_error.read().decode()
                        body = json.loads(raw)
                        last_error = body.get('reason', '') or body.get('error', '') or raw[:200]
                    except Exception:
                        last_error = str(http_error)
                    tk.messagebox.showerror(
                        '激活失败', f'服务器错误（{http_error.code}）：{last_error}'
                    )
                    return False
                except Exception:
                    continue
            tk.messagebox.showerror('激活失败', '无法连接激活服务器，请检查网络后重试')
        except Exception as exc:
            tk.messagebox.showerror('激活失败', f'未知错误：{exc}')
        return False

    def heartbeat():
        global _act_type, _act_exp
        time.sleep(5)
        while True:
            time.sleep(300)
            try:
                import urllib.request as request
                try:
                    from ke_engine import stable_hwid as current_hwid
                    hwid = current_hwid()
                except Exception:
                    hwid = hashlib.md5(
                        (str(_uuid.getnode()) + os.environ.get('COMPUTERNAME', '')).encode()
                    ).hexdigest()[:12]
                payload = json.dumps({'key': _act_key, 'hwid': hwid}).encode()
                for server in servers:
                    if not server:
                        continue
                    try:
                        query = request.Request(
                            f'{server}/ping',
                            data=payload,
                            headers={'Content-Type': 'application/json'},
                        )
                        response = json.loads(request.urlopen(query, timeout=3).read())
                        if response.get('ok') and verify_resp(response, _act_key, hwid):
                            new_type = response.get('type', '')
                            new_exp = response.get('expires', '')
                            if new_type:
                                _act_type = new_type
                            if new_exp:
                                _act_exp = new_exp
                            settings = load_settings()
                            settings['activate_type'] = _act_type
                            settings['activate_exp'] = _act_exp
                            save_settings(settings)
                            write_act_cache(
                                os.path.join(SCRIPT_DIR, '激活缓存'),
                                response,
                                _act_key,
                                hwid,
                            )
                            break
                        reason = response.get('reason', '')
                        if '禁用' in reason or '删除' in reason or '过期' in reason:
                            activation_cache = os.path.join(SCRIPT_DIR, '激活缓存')
                            if os.path.exists(activation_cache):
                                os.remove(activation_cache)
                            settings = load_settings()
                            settings['activate_type'] = ''
                            settings['activate_exp'] = ''
                            save_settings(settings)
                            _act_type = ''
                            _act_exp = ''
                        break
                    except Exception:
                        continue
            except Exception:
                pass

    threading.Thread(target=heartbeat, daemon=True).start()

    def send_telemetry(event, script='', error='', duration=0):
        def worker():
            try:
                import urllib.request as request
                try:
                    from ke_collect import VERSION
                except Exception:
                    VERSION = 'v26.8.21'
                payload = json.dumps(
                    {
                        'key': _act_key,
                        'hwid': _act_hwid,
                        'event': event,
                        'script': script,
                        'error': error,
                        'duration': duration,
                        'version': VERSION,
                    }
                ).encode()
                for server in servers:
                    if not server:
                        continue
                    try:
                        query = request.Request(
                            f'{server}/telemetry',
                            data=payload,
                            headers={'Content-Type': 'application/json'},
                        )
                        request.urlopen(query, timeout=3)
                        return
                    except Exception:
                        continue
            except Exception:
                return

        threading.Thread(target=worker, daemon=True).start()

    send_telemetry('startup', script=load_settings().get('last_driver', ''))
    return show_activate_dialog
