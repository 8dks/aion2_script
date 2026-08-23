"""
KE Driver Mem 读取 — 纯 Python ctypes 直调 Windows API
无 C 编译器依赖，无外部 DLL，性能等同 C 扩展
"""
import ctypes
from ctypes import wintypes
import os
import re
import struct
import threading
import time
PROCESS_VM_READ = 16
PROCESS_VM_OPERATION = 8
PROCESS_QUERY_INFORMATION = 1024
PROCESS_VM_WRITE = 32
TH32CS_SNAPMODULE = 8
TH32CS_SNAPMODULE32 = 16

class MODULEENTRY32W(ctypes.Structure):
    _fields_ = [('dwSize', wintypes.DWORD), ('th32ModuleID', wintypes.DWORD), ('th32ProcessID', wintypes.DWORD), ('GlblcntUsage', wintypes.DWORD), ('ProccntUsage', wintypes.DWORD), ('modBaseAddr', ctypes.c_void_p), ('modBaseSize', wintypes.DWORD), ('hModule', wintypes.HMODULE), ('szModule', ctypes.c_wchar * 256), ('szExePath', ctypes.c_wchar * 260)]
MEM_COMMIT = 4096
PAGE_NOACCESS = 1
PAGE_READONLY = 2
PAGE_READWRITE = 4
PAGE_WRITECOPY = 8
PAGE_EXECUTE = 16
PAGE_EXECUTE_READ = 32
PAGE_EXECUTE_READWRITE = 64
PAGE_EXECUTE_WRITECOPY = 128
PAGE_GUARD = 256
PAGE_NOCACHE = 512
READABLE_PAGES = {PAGE_READONLY, PAGE_READWRITE, PAGE_WRITECOPY, PAGE_EXECUTE_READ, PAGE_EXECUTE_READWRITE, PAGE_EXECUTE_WRITECOPY}

class MEMORY_BASIC_INFORMATION(ctypes.Structure):
    _fields_ = [('BaseAddress', ctypes.c_void_p), ('AllocationBase', ctypes.c_void_p), ('AllocationProtect', wintypes.DWORD), ('PartitionId', wintypes.WORD), ('RegionSize', ctypes.c_size_t), ('State', wintypes.DWORD), ('Protect', wintypes.DWORD), ('Type', wintypes.DWORD)]
KE_TYPES = {'u8': 1, 'u16': 2, 'u32': 3, 'u64': 4, 'i8': 5, 'i16': 6, 'i32': 7, 'i64': 8, 'f32': 9, 'f64': 10}
KE_TYPE_SIZES = {'u8': 1, 'u16': 2, 'u32': 4, 'u64': 8, 'i8': 1, 'i16': 2, 'i32': 4, 'i64': 8, 'f32': 4, 'f64': 8}
KE_ERR_TEXT = {5: '拒绝访问(需管理员权限/被安全软件拦截)', 6: '进程已退出', 87: '参数错误', 299: '部分读取', 1168: '模块未找到', 127: '未找到', 2147483649: '未找到目标窗口', 2147483650: '窗口枚举失败', 2147483651: '绑定窗口句柄失效(窗口已关闭), 请重开游戏窗口'}

def _err_text(code):
    """Windows 错误码 → 中文说明。"""
    if code in KE_ERR_TEXT:
        return KE_ERR_TEXT[code]
    try:
        buf = ctypes.create_unicode_buffer(256)
        ctypes.windll.kernel32.FormatMessageW(4096, None, code, 0, buf, len(buf), None)
        return buf.value.replace('\r\n', ' ').strip()
    except Exception:
        return f'错误码{code}'

class MemReadError(Exception):
    """Mem 读取异常。"""

    def __init__(self, code, addr=0):
        self.code = code
        self.addr = addr
        super().__init__(f'Mem 读取失败 [{_err_text(code)}] @ 0x{addr:X}')

def _init_kernel32():
    """初始化 kernel32 API 函数签名（性能关键）。"""
    k32 = ctypes.windll.kernel32
    k32.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
    k32.OpenProcess.restype = wintypes.HANDLE
    k32.CloseHandle.argtypes = [wintypes.HANDLE]
    k32.CloseHandle.restype = wintypes.BOOL
    k32.ReadProcessMemory.argtypes = [wintypes.HANDLE, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_size_t, ctypes.POINTER(ctypes.c_size_t)]
    k32.ReadProcessMemory.restype = wintypes.BOOL
    k32.VirtualQueryEx.argtypes = [wintypes.HANDLE, ctypes.c_void_p, ctypes.POINTER(MEMORY_BASIC_INFORMATION), ctypes.c_size_t]
    k32.VirtualQueryEx.restype = ctypes.c_size_t
    k32.GetLastError.argtypes = []
    k32.GetLastError.restype = wintypes.DWORD
    k32.IsWow64Process.argtypes = [wintypes.HANDLE, ctypes.POINTER(wintypes.BOOL)]
    k32.IsWow64Process.restype = wintypes.BOOL
    k32.CreateToolhelp32Snapshot.argtypes = [wintypes.DWORD, wintypes.DWORD]
    k32.CreateToolhelp32Snapshot.restype = wintypes.HANDLE
    k32.Module32FirstW.argtypes = [wintypes.HANDLE, ctypes.POINTER(MODULEENTRY32W)]
    k32.Module32FirstW.restype = wintypes.BOOL
    k32.Module32NextW.argtypes = [wintypes.HANDLE, ctypes.POINTER(MODULEENTRY32W)]
    k32.Module32NextW.restype = wintypes.BOOL
    try:
        k32.IsWow64Process2.argtypes = [wintypes.HANDLE, ctypes.POINTER(wintypes.USHORT), ctypes.POINTER(wintypes.USHORT)]
        k32.IsWow64Process2.restype = wintypes.BOOL
    except Exception:
        pass
    u32 = ctypes.windll.user32
    u32.GetWindowThreadProcessId.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.DWORD)]
    u32.GetWindowThreadProcessId.restype = wintypes.DWORD
    return (k32, u32)
_k32, _u32 = _init_kernel32()

class KeMem:
    """进程 Mem 读取器 — 纯 Python ctypes 实现。"""

    def __init__(self, log_cb=None):
        self._log = log_cb or (lambda _message: None)
        self._hProc = None
        self._pid = 0
        self._bits = None
        self._title = ''
        self._hwnd = 0
        self._lock = threading.Lock()
        self._module_cache = {}
        self._fail_count = 0
        self._max_fails = 20
        self._last_err_code = 0
        self._reconnect_enabled = True

    def attach_by_pid(self, pid):
        if pid:
            if int(pid) <= 0:
                self._last_err_code = 2147483651
                self._log_fail_once('[Mem] 无效 PID(0)')
                return False
        else:
            self._last_err_code = 2147483651
            self._log_fail_once('[Mem] 无效 PID(0)')
            return False
        with self._lock as __temp_4292:
            if self._hProc:
                _k32.CloseHandle(self._hProc)
                self._hProc = None
            self._pid = 0
            self._bits = None
            self._last_err_code = 0
            self._hProc = _k32.OpenProcess(PROCESS_QUERY_INFORMATION | PROCESS_VM_READ, False, int(pid))
            if not self._hProc:
                self._last_err_code = _k32.GetLastError()
                self._log_fail_once('[Mem] OpenProcess 失败: ' + str(_err_text(self._last_err_code)) + '(重试中, 恢复前静默)')
                return False
            self._pid = int(pid)
            self._bits = self._detect_bitness()
            self._module_cache.clear()
            self._fail_count = 0
            self._last_err_code = 0
            self._attach_fail_logged = False
            if self._bits == 1:
                _bits_txt = '64'
            elif self._bits == 0:
                _bits_txt = '32'
            else:
                _bits_txt = '未知'
            self._log('[Mem] 已附加 PID=' + str(pid) + ' (' + str(_bits_txt) + '位)')
            return True
        return None

    def attach_by_hwnd(self, hwnd):
        if not hwnd:
            self._last_err_code = 87
            self._log_fail_once('[Mem] 无效窗口句柄(0)')
            return False
        self._hwnd = int(hwnd)
        pid = wintypes.DWORD()
        _u32.GetWindowThreadProcessId(self._hwnd, ctypes.byref(pid))
        if not pid.value:
            self._last_err_code = 2147483651
            self._log_fail_once('[Mem] 窗口句柄失效(窗口可能已关闭), 请重开游戏窗口后重试')
            return False
        return self.attach_by_pid(pid.value)

    def attach_by_title(self, title):
        """通过窗口标题查找窗口并附加。"""
        import ctypes as _ct
        self._title = title
        result = []
        wnd_enum_proc = _ct.WINFUNCTYPE(_ct.c_bool, _ct.c_void_p, _ct.c_void_p)

        def callback(hwnd, _):
            try:
                buf = _ct.create_unicode_buffer(256)
                _ct.windll.user32.GetWindowTextW(hwnd, buf, 256)
                text = buf.value
                if text and title and (title.lower() in text.lower()):
                    result.append(hwnd)
                    return False
            except Exception:
                pass
            return True
        try:
            _ct.windll.user32.EnumWindows(wnd_enum_proc(callback), 0)
        except Exception as exc:
            self._last_err_code = 2147483650
            self._log(f'[Mem] EnumWindows失败: {exc}')
            return False
        if result:
            self._hwnd = result[0]
            return self.attach_by_hwnd(self._hwnd)
        self._last_err_code = 2147483649
        self._log(f'[Mem] 未找到窗口: {title}')
        return False

    def close(self):
        with self._lock:
            if self._hProc:
                _k32.CloseHandle(self._hProc)
                self._hProc = None
            self._pid = 0
            self._bits = None
            self._module_cache.clear()
            self._fail_count = 0
            self._last_err_code = 0

    @property
    def attached(self):
        return self._hProc is not None

    @property
    def pid(self):
        return self._pid

    @property
    def bits(self):
        return self._bits

    @property
    def last_error(self):
        return self._last_err_code

    @property
    def last_error_text(self):
        return _err_text(self._last_err_code)

    def _detect_bitness(self):
        if not self._hProc:
            return None
        psapi = ctypes.WinDLL('psapi.dll')
        psapi.EnumProcessModules.argtypes = [wintypes.HANDLE, ctypes.POINTER(ctypes.c_void_p), wintypes.DWORD, ctypes.POINTER(wintypes.DWORD)]
        psapi.EnumProcessModules.restype = ctypes.c_int
        hmods = (ctypes.c_void_p * 1)()
        needed = wintypes.DWORD()
        if psapi.EnumProcessModules(self._hProc, hmods, ctypes.sizeof(hmods), ctypes.byref(needed)):
            base_addr = int(hmods[0])
            pe_off = self._read_raw_u32(base_addr + 60)
            if pe_off is not None:
                magic = self._read_raw_u16(base_addr + pe_off + 24)
                if magic is not None:
                    if magic == 523:
                        return 1
                    else:
                        return 0
        wow = wintypes.BOOL()
        if _k32.IsWow64Process(self._hProc, ctypes.byref(wow)):
            if wow.value:
                return 0
            else:
                return 1
        struct = __import__('struct', fromlist=None, level=0)
        if struct.calcsize('P') == 8:
            return 1
        else:
            return 0

    def _read_raw_u32(self, addr):
        buf = ctypes.create_string_buffer(4)
        read = ctypes.c_size_t()
        if _k32.ReadProcessMemory(self._hProc, ctypes.c_void_p(addr), buf, 4, ctypes.byref(read)):
            return struct.unpack('<I', buf.raw[:4])[0]
        return None

    def _read_raw_u16(self, addr):
        buf = ctypes.create_string_buffer(2)
        read = ctypes.c_size_t()
        if _k32.ReadProcessMemory(self._hProc, ctypes.c_void_p(addr), buf, 2, ctypes.byref(read)):
            return struct.unpack('<H', buf.raw[:2])[0]
        return None

    def module_base(self, name=None):
        """获取模块基址，返回 ``(base, size)`` 或 ``(None, None)``。"""
        cache_key = name or '__main__'
        if cache_key in self._module_cache:
            return self._module_cache[cache_key]
        if not self._hProc or not self._pid:
            return (None, None)
        try:
            psapi = ctypes.WinDLL('psapi.dll')
            psapi.EnumProcessModules.argtypes = [wintypes.HANDLE, ctypes.POINTER(ctypes.c_void_p), wintypes.DWORD, ctypes.POINTER(wintypes.DWORD)]
            psapi.EnumProcessModules.restype = ctypes.c_int
            psapi.GetModuleBaseNameW.argtypes = [wintypes.HANDLE, ctypes.c_void_p, ctypes.c_wchar_p, wintypes.DWORD]
            psapi.GetModuleBaseNameW.restype = ctypes.c_uint32
            max_modules = 1024
            modules = (ctypes.c_void_p * max_modules)()
            needed = wintypes.DWORD()
            if not psapi.EnumProcessModules(self._hProc, modules, ctypes.sizeof(modules), ctypes.byref(needed)):
                return (None, None)
            count = needed.value // ctypes.sizeof(ctypes.c_void_p)
            for index in range(count):
                name_buf = ctypes.create_unicode_buffer(260)
                psapi.GetModuleBaseNameW(self._hProc, modules[index], name_buf, 260)
                module_name = name_buf.value
                base_addr = int(modules[index])
                try:
                    pe_offset = self.read_u32(base_addr + 60)
                    if pe_offset:
                        size = self.read_u32(base_addr + pe_offset + 80)
                        if size is None:
                            size = 0
                    else:
                        size = 0
                except Exception:
                    size = 0
                if name is None and index == 0:
                    self._module_cache[cache_key] = (base_addr, size)
                    return (base_addr, size)
                if name is not None and module_name.lower() == name.lower():
                    self._module_cache[cache_key] = (base_addr, size)
                    return (base_addr, size)
                self._module_cache[module_name] = (base_addr, size)
        except Exception as exc:
            self._log(f'[Mem] module_base异常: {exc}')
        return (None, None)

    def _resolve_base(self, base_spec):
        """解析整数、十六进制文本或“模块名+偏移”为绝对地址。"""
        if isinstance(base_spec, int):
            return base_spec
        value = str(base_spec).strip() if base_spec else ''
        if not value:
            return None
        if value.startswith(('0x', '0X')):
            try:
                return int(value, 16)
            except Exception:
                return None
        match = re.match('^(.+?)\\s*\\+\\s*(0x[0-9a-fA-F]+|\\d+)$', value)
        if match:
            module_name = match.group(1).strip()
            offset_text = match.group(2).strip()
            offset = int(offset_text, 16) if offset_text.startswith('0x') else int(offset_text)
            if module_name.lower() in ('main', ''):
                module_name = None
            base, _ = self.module_base(module_name)
            return base + offset if base else None
        base, _ = self.module_base(value)
        return base

    def _rpm(self, addr, size):
        """ReadProcessMemory，返回读取到的字节或 ``None``。"""
        with self._lock:
            if not self._hProc:
                return None
            addr = int(addr)
            buf = ctypes.create_string_buffer(size)
            bytes_read = ctypes.c_size_t(0)
            ok = _k32.ReadProcessMemory(self._hProc, ctypes.c_void_p(addr), buf, size, ctypes.byref(bytes_read))
            if not ok:
                self._last_err_code = _k32.GetLastError()
                return None
            self._last_err_code = 299 if bytes_read.value < size else 0
            return buf.raw[:bytes_read.value]

    def read_bytes(self, addr, size):
        addr = self._resolve_base(addr) if isinstance(addr, str) else addr
        if addr is None:
            return None
        data = self._rpm(addr, size)
        if data:
            self._fail_count = 0
        else:
            self._on_fail()
        return data

    def _read_num(self, addr, fmt_char, size):
        addr = self._resolve_base(addr) if isinstance(addr, str) else addr
        if addr is None:
            return None
        data = self._rpm(addr, size)
        if data is None or len(data) < size:
            self._on_fail()
            return None
        self._fail_count = 0
        self._last_err_code = 0
        return struct.unpack(f'<{fmt_char}', data[:size])[0]

    def read_u8(self, addr):
        return self._read_num(addr, 'B', 1)

    def read_u16(self, addr):
        return self._read_num(addr, 'H', 2)

    def read_u32(self, addr):
        return self._read_num(addr, 'I', 4)

    def read_u64(self, addr):
        return self._read_num(addr, 'Q', 8)

    def read_i8(self, addr):
        return self._read_num(addr, 'b', 1)

    def read_i16(self, addr):
        return self._read_num(addr, 'h', 2)

    def read_i32(self, addr):
        return self._read_num(addr, 'i', 4)

    def read_i64(self, addr):
        return self._read_num(addr, 'q', 8)

    def read_f32(self, addr):
        return self._read_num(addr, 'f', 4)

    def read_f64(self, addr):
        return self._read_num(addr, 'd', 8)

    def read_ptr(self, addr):
        size = 8 if self._bits else 4
        addr = self._resolve_base(addr) if isinstance(addr, str) else addr
        if addr is None:
            return None
        data = self._rpm(addr, size)
        if data is None or len(data) < size:
            self._on_fail()
            return None
        self._fail_count = 0
        self._last_err_code = 0
        return struct.unpack('<Q' if size == 8 else '<I', data[:size])[0]

    def read_str(self, addr, maxlen=256):
        addr = self._resolve_base(addr) if isinstance(addr, str) else addr
        if addr is None:
            return None
        result = bytearray()
        current = addr
        while len(result) < maxlen:
            chunk = self._rpm(current, min(64, maxlen - len(result)))
            if not chunk:
                break
            for byte in chunk:
                if byte == 0:
                    try:
                        return result.decode('utf-8', errors='replace')
                    except Exception:
                        return result.decode('latin-1', errors='replace')
                result.append(byte)
                if len(result) >= maxlen:
                    break
            current += len(chunk)
        try:
            return result.decode('utf-8', errors='replace')
        except Exception:
            return result.decode('latin-1', errors='replace')

    def read_wstr(self, addr, maxlen=256):
        addr = self._resolve_base(addr) if isinstance(addr, str) else addr
        if addr is None:
            return None
        result = []
        current = addr
        while len(result) < maxlen:
            chunk = self._rpm(current, 128)
            if not chunk:
                break
            for index in range(0, len(chunk) - 1, 2):
                character = struct.unpack('<H', chunk[index:index + 2])[0]
                if character == 0:
                    return ''.join((chr(item) for item in result))
                result.append(character)
                if len(result) >= maxlen:
                    break
            current += len(chunk)
        return ''.join((chr(item) for item in result))

    def chain(self, base, offsets):
        if isinstance(base, str):
            base = self._resolve_base(base)
        if base is None:
            return None
        addr = base
        for offset in offsets:
            pointer = self.read_ptr(addr)
            if pointer is None or pointer == 0:
                return None
            addr = pointer + offset
        return addr

    def chain_read(self, base, offsets, dtype='i32'):
        if dtype in ('str', 'wstr'):
            addr = self.chain(base, offsets) if offsets else self._resolve_base(base)
            if addr is None:
                return None
            return self.read_str(addr) if dtype == 'str' else self.read_wstr(addr)
        if dtype == 'ptr':
            addr = self.chain(base, offsets) if offsets else self._resolve_base(base)
            return self.read_ptr(addr) if addr is not None else None
        if dtype.startswith('bytes:'):
            try:
                length = int(dtype.split(':')[1])
            except (ValueError, IndexError):
                return None
            addr = self.chain(base, offsets) if offsets else self._resolve_base(base)
            return self.read_bytes(addr, length) if addr is not None else None
        if isinstance(base, str):
            base = self._resolve_base(base)
        if base is None:
            return None
        addr = base
        if offsets:
            for offset in offsets:
                pointer = self.read_ptr(addr)
                if pointer is None or pointer == 0:
                    self._on_fail()
                    return None
                addr = pointer + offset
        readers = {'u8': self.read_u8, 'u16': self.read_u16, 'u32': self.read_u32, 'u64': self.read_u64, 'i8': self.read_i8, 'i16': self.read_i16, 'i32': self.read_i32, 'i64': self.read_i64, 'f32': self.read_f32, 'f64': self.read_f64}
        function = readers.get(dtype)
        if function is None:
            self._log(f'[Mem] 未知类型: {dtype}')
            return None
        return function(addr)

    def aob_scan(self, pattern_str, start=0, size=2147483647, max_results=50):
        parts = pattern_str.strip().split()
        pattern = []
        mask = []
        for part in parts:
            value = part[2:] if part.lower().startswith('0x') else part
            if value in ('??', '?'):
                pattern.append(0)
                mask.append(0)
            else:
                pattern.append(int(value, 16))
                mask.append(255)
        if not pattern:
            return []
        if isinstance(start, str):
            start = self._resolve_base(start) or 0
        pattern_length = len(pattern)
        results = []
        current = start
        end = start + size
        chunk_size = 4096
        carry = 0
        buffer = bytearray(chunk_size + pattern_length)
        while current < end and len(results) < (max_results or 99999):
            to_read = min(chunk_size, end - current)
            if to_read < pattern_length:
                break
            data = self._rpm(current, to_read)
            if not data or len(data) < to_read:
                current += to_read
                carry = 0
                continue
            search_buffer = buffer[:carry] + data if carry > 0 else data
            for index in range(len(search_buffer) - pattern_length + 1):
                matched = True
                for pattern_index in range(pattern_length):
                    if mask[pattern_index] and search_buffer[index + pattern_index] != pattern[pattern_index]:
                        matched = False
                        break
                if matched:
                    results.append(current + index - carry)
                    if max_results and len(results) >= max_results:
                        break
            if max_results is None or len(results) < max_results:
                carry = pattern_length - 1
                if carry > len(data):
                    carry = len(data)
                buffer[:carry] = data[-carry:]
                current += to_read - carry
            else:
                break
        self._fail_count = 0
        return results

    def _on_fail(self):
        self._fail_count += 1
        if self._fail_count >= self._max_fails and self._reconnect_enabled:
            self._log(f'[Mem] 连续失败{self._fail_count}次, 尝试重连...')
            self._fail_count = 0
            if self._title:
                self.attach_by_title(self._title)
            elif self._hwnd:
                self.attach_by_hwnd(self._hwnd)

    def _on_ok(self):
        self._fail_count = 0
        self._last_err_code = 0

    def scan_regions(self, dtype='i32'):
        regions = []
        addr = ctypes.c_void_p(0)
        info = MEMORY_BASIC_INFORMATION()
        info_size = ctypes.sizeof(MEMORY_BASIC_INFORMATION)
        while True:
            result = _k32.VirtualQueryEx(self._hProc, addr, ctypes.byref(info), info_size)
            if result == 0:
                break
            if info.State == MEM_COMMIT and info.Protect in READABLE_PAGES and (info.RegionSize > 0):
                regions.append((int(info.BaseAddress or 0), info.RegionSize))
            next_addr = int(info.BaseAddress or 0) + info.RegionSize
            if next_addr <= int(info.BaseAddress or 0):
                break
            addr = ctypes.c_void_p(next_addr)
        return regions

    def scan_value(self, start, size, dtype='i32', progress_cb=None):
        type_size = KE_TYPE_SIZES.get(dtype, 4)
        results = []
        current = start
        end = start + size
        chunk_size = 4096
        scanned = 0
        while current < end:
            to_read = min(chunk_size, end - current)
            data = self._rpm(current, to_read)
            if data:
                for index in range(0, len(data) - type_size + 1, type_size):
                    results.append((current + index, bytes(data[index:index + type_size])))
            current += to_read
            scanned += to_read
            if progress_cb and scanned % (chunk_size * 32) == 0:
                progress_cb(scanned, size)
        return results

    def scan_filter_changed(self, prev_results, dtype='i32', progress_cb=None):
        type_size = KE_TYPE_SIZES.get(dtype, 4)
        changed = []
        total = len(prev_results)
        for index, (addr, old_bytes) in enumerate(prev_results):
            new_data = self._rpm(addr, type_size)
            if new_data and new_data != old_bytes:
                changed.append((addr, old_bytes, new_data))
            if progress_cb and index % 5000 == 0:
                progress_cb(index, total)
        return changed

    def scan_memory_for_value(self, dtype='i32', target_value=1, max_regions=50, progress_cb=None):
        regions = self.scan_regions(dtype)
        type_size = KE_TYPE_SIZES.get(dtype, 4)
        formats = {'u8': '<B', 'u16': '<H', 'u32': '<I', 'u64': '<Q', 'i8': '<b', 'i16': '<h', 'i32': '<i', 'i64': '<q', 'f32': '<f', 'f64': '<d'}
        target_bytes = struct.pack(formats.get(dtype, '<i'), target_value)
        results = []
        total_size = sum((size for _, size in regions[:max_regions]))
        scanned_size = 0
        for start, size in regions[:max_regions]:
            current = start
            end = start + size
            while current < end:
                to_read = min(4096, end - current)
                data = self._rpm(current, to_read)
                if data:
                    for index in range(len(data) - type_size + 1):
                        if data[index:index + type_size] == target_bytes:
                            results.append(current + index)
                current += to_read
            scanned_size += size
            if progress_cb:
                percent = min(99, int(scanned_size / max(1, total_size) * 100))
                progress_cb(percent, len(results))
        if progress_cb:
            progress_cb(100, len(results))
        return results

    def refine_candidates(self, candidates, dtype='i32', target_value=None, progress_cb=None):
        type_size = KE_TYPE_SIZES.get(dtype, 4)
        formats = {'u8': '<B', 'u16': '<H', 'u32': '<I', 'u64': '<Q', 'i8': '<b', 'i16': '<h', 'i32': '<i', 'i64': '<q', 'f32': '<f', 'f64': '<d'}
        surviving = []
        total = len(candidates)
        for index, addr in enumerate(candidates):
            data = self._rpm(addr, type_size)
            if data:
                if target_value is None or data == struct.pack(formats.get(dtype, '<i'), target_value):
                    surviving.append(addr)
            if progress_cb and index % 2000 == 0:
                progress_cb(index, total)
        return surviving

    def _log_fail_once(self, msg):
        if not self._attach_fail_logged:
            self._attach_fail_logged = True
            self._log(msg)
            return None
        return None
if __name__ == '__main__':
    import win32gui

    def find_window(title_part):
        result = []

        def callback(hwnd, _):
            if title_part.lower() in win32gui.GetWindowText(hwnd).lower():
                result.append(hwnd)
                return False
            return True
        win32gui.EnumWindows(callback, None)
        return result[0] if result else None
    hwnd = find_window('AION2')
    if not hwnd:
        print('未找到目标窗口，尝试当前前台窗口...')
        hwnd = win32gui.GetForegroundWindow()
    print(f'窗口: {win32gui.GetWindowText(hwnd)}')
    memory = KeMem()
    if memory.attach_by_hwnd(hwnd):
        print(f'PID={memory.pid} {memory.bits}位')
        base, size = memory.module_base()
        if base:
            print(f'主模块: 0x{base:X} ({size / 1024 / 1024:.1f}MB)')
            preview = memory.read_bytes(base, 64)
            if preview:
                print(f'头部: {preview[:32].hex()}')
    else:
        print(f'失败: {memory.last_error_text}')
    memory.close()
