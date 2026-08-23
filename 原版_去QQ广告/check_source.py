"""检查原版去广告源码的语法和运行资源。"""

from __future__ import annotations

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


def main() -> int:
    errors: list[str] = []
    for name in MODULES:
        path = ROOT / name
        if not path.is_file():
            errors.append(f"缺少源码：{name}")
            continue
        try:
            compile(path.read_text(encoding="utf-8-sig"), str(path), "exec")
        except Exception as exc:
            errors.append(f"源码语法错误：{name}: {exc}")

    for name in RESOURCES:
        if not (ROOT / name).is_file():
            errors.append(f"缺少资源：{name}")

    try:
        json.loads((ROOT / "设置.json").read_text(encoding="utf-8-sig"))
    except Exception as exc:
        errors.append(f"设置.json 无效：{exc}")

    dd_text = (ROOT / "DD.py").read_text(encoding="utf-8-sig")
    for marker in ("qm.qq.com", "tencent://", "Q聊"):
        if marker in dd_text:
            errors.append(f"仍存在 QQ 广告标记：{marker}")

    if errors:
        print("检查失败：")
        for error in errors:
            print(f"  - {error}")
        return 1
    print(f"检查通过：{len(MODULES)} 个源码文件语法正确，必要资源齐全，QQ 广告入口已移除。")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
