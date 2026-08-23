# -*- mode: python ; coding: utf-8 -*-

from pathlib import Path


ROOT = Path(SPECPATH)


def resource(source: str, target: str = "."):
    return (str(ROOT / source), target)


datas = [
    resource("设置.json"),
    resource("captcha_model.pkl"),
    resource("内置规则.dat"),
    resource("icon_main.ico"),
    resource("keymod.dll"),
    resource("F.dll"),
    resource("DD64.dll"),
    resource("DDHID64.dll"),
    resource("devcon.exe"),
    resource("ttinput.cat"),
    resource("ttinput.dll"),
    resource("ttinput.inf"),
    resource("ttinput.sys"),
    resource("USBip-0.9.7.7-x64-release.exe"),
    resource("models", "models"),
    resource("tessdata", "tessdata"),
    resource("驱动", "驱动"),
    resource("FakerInput", "FakerInput"),
    resource("VIIPER", "VIIPER"),
]

hiddenimports = [
    "captcha_service",
    "captcha_yolo",
    "captcha_ocr",
    "quick_recognition",
    "ke_ai",
    "ke_mem",
    "captcha_ai",
    "captcha_ai_train",
    "ke_engine",
    "ke_collect",
    "ke_sentinel",
    "ke_core",
    "Crypto.Cipher.AES",
    "Crypto.Cipher.ChaCha20_Poly1305",
    "dxcam",
    "edge_tts",
    "interception",
    "lupa",
    "onnxruntime",
    "pytesseract",
    "requests",
    "win32api",
    "win32con",
    "win32gui",
    "win32ui",
    "win32com.client",
    "pythoncom",
    "pywintypes",
]

a = Analysis(
    [str(ROOT / "DD.py")],
    pathex=[str(ROOT)],
    binaries=[],
    datas=datas,
    hiddenimports=hiddenimports,
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    excludes=["matplotlib", "pandas", "scipy", "torch"],
    noarchive=False,
    optimize=0,
)
pyz = PYZ(a.pure)

exe = EXE(
    pyz,
    a.scripts,
    a.binaries,
    a.datas,
    [],
    name="K3M2_永久版",
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=True,
    upx_exclude=[],
    runtime_tmpdir=None,
    console=False,
    disable_windowed_traceback=False,
    argv_emulation=False,
    target_arch=None,
    codesign_identity=None,
    entitlements_file=None,
    icon=str(ROOT / "icon_main.ico"),
)
