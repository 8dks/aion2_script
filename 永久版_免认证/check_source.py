"""检查永久版源码的语法、资源与离线授权入口。"""

from __future__ import annotations

import ast
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent
MODULES = (
    "DD.py",
    "captcha_service.py",
    "captcha_yolo.py",
    "captcha_ocr.py",
    "quick_recognition.py",
    "ke_ai.py",
    "ke_mem.py",
    "captcha_ai.py",
    "captcha_ai_train.py",
    "ke_engine.py",
    "ke_collect.py",
    "ke_sentinel.py",
    "ke_core.py",
)
RESOURCES = (
    "设置.json",
    "captcha_model.pkl",
    "F.dll",
    "DD64.dll",
    "DDHID64.dll",
    "keymod.dll",
    "devcon.exe",
    "ttinput.dll",
    "ttinput.inf",
    "ttinput.sys",
    "内置规则.dat",
    "models/captcha_ocr.onnx",
    "models/captcha_presence_yolov5.onnx",
    "models/ocr_angle.onnx",
    "models/ocr_det.onnx",
    "tessdata/tessdata-main/eng.traineddata",
    "tessdata/tessdata-main/chi_sim.traineddata",
    "tessdata/tessdata-main/chi_tra.traineddata",
    "VIIPER/viiper.exe",
    "FakerInput/FakerInput.dll",
)


def class_method(tree: ast.Module, class_name: str, method_name: str) -> ast.FunctionDef | None:
    for node in tree.body:
        if isinstance(node, ast.ClassDef) and node.name == class_name:
            for item in node.body:
                if isinstance(item, ast.FunctionDef) and item.name == method_name:
                    return item
    return None


def starts_with_return(function: ast.FunctionDef | None) -> bool:
    if function is None or not function.body:
        return False
    index = 1 if isinstance(function.body[0], ast.Expr) and isinstance(function.body[0].value, ast.Constant) and isinstance(function.body[0].value.value, str) else 0
    return index < len(function.body) and isinstance(function.body[index], ast.Return)


def main() -> int:
    errors: list[str] = []
    sources: dict[str, str] = {}
    for name in MODULES:
        path = ROOT / name
        if not path.is_file():
            errors.append(f"缺少源码：{name}")
            continue
        try:
            text = path.read_text(encoding="utf-8-sig")
            compile(text, str(path), "exec")
            sources[name] = text
        except Exception as exc:
            errors.append(f"源码语法错误：{name}: {exc}")

    for name in RESOURCES:
        if not (ROOT / name).is_file():
            errors.append(f"缺少资源：{name}")

    try:
        settings = json.loads((ROOT / "设置.json").read_text(encoding="utf-8-sig"))
        expected = {
            "activate_key": "LOCAL-PERMANENT",
            "activate_type": "永久版",
            "activate_exp": "永久",
            "is_admin": True,
        }
        for key, value in expected.items():
            if settings.get(key) != value:
                errors.append(f"永久授权默认值不正确：{key}")
    except Exception as exc:
        errors.append(f"设置.json 无效：{exc}")

    all_source = "\n".join(sources.values())
    for marker in ("47.79.117.138", "qm.qq.com", "tencent://", "Q聊", "live.douyin.com", "dy_live_label"):
        if marker in all_source:
            errors.append(f"仍存在已禁用的远程/广告标记：{marker}")

    if "DD.py" in sources:
        tree = ast.parse(sources["DD.py"], "DD.py")
        for name in ("_online_verify_silent", "_show_activate_dialog", "_heartbeat", "_send_telemetry"):
            if not starts_with_return(class_method(tree, "App", name)):
                errors.append(f"永久版兼容入口未在本地直接返回：App.{name}")
        start_method = class_method(tree, "App", "_do_start")
        start_dump = ast.dump(start_method) if start_method else ""
        if "_verify_ok_continue" not in start_dump or "_online_verify_silent" in start_dump:
            errors.append("启动流程仍包含在线授权门禁")

    if errors:
        print("检查失败：")
        for error in errors:
            print(f"  - {error}")
        return 1
    print(f"检查通过：{len(MODULES)} 个源码文件语法正确，资源齐全，永久版离线授权入口有效。")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
