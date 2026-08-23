"""验证码 AI 检测与历史模型兼容推理。"""
from __future__ import annotations
import os
import pickle
import sys
import threading
import numpy as np

def _find_model_dir():
    candidates = []
    if getattr(sys, 'frozen', False):
        candidates.append(os.path.dirname(os.path.abspath(sys.executable)))
        candidates.append(getattr(sys, '_MEIPASS', ''))
    candidates.append(os.path.dirname(os.path.abspath(__file__)))
    for directory in candidates:
        if directory and os.path.isfile(os.path.join(directory, 'captcha_model.pkl')):
            return directory
    return candidates[-1]

SCRIPT_DIR = _find_model_dir()
MODEL_FILE = os.path.join(SCRIPT_DIR, 'captcha_model.pkl')
XML_FILE = os.path.join(SCRIPT_DIR, 'captcha_model.xml')
_model = None
_img_size = None
_xml_cache = None
_load_lock = threading.Lock()
_load_failed = False
F_PARAM1 = 2.0 / 3.0
F_PARAM2 = 1.7159

def reload_model():
    """清除进程级模型缓存，使下次预测重新读取训练结果。"""
    global _model, _img_size, _xml_cache, _load_failed
    _model = None
    _img_size = None
    _xml_cache = None
    _load_failed = False

def _xml_load_path():
    """把中文路径中的 XML 模型复制到英文临时目录后返回加载路径。"""
    global _xml_cache
    if _xml_cache:
        return _xml_cache
    if not os.path.exists(XML_FILE):
        return None
    try:
        import shutil
        import tempfile
        directory = os.path.join(tempfile.gettempdir(), 'ke_captcha_model')
        os.makedirs(directory, exist_ok=True)
        destination = os.path.join(directory, 'captcha_model.xml')
        if not os.path.exists(destination) or os.path.getmtime(destination) < os.path.getmtime(XML_FILE):
            shutil.copy2(XML_FILE, destination)
        _xml_cache = destination
        return destination
    except Exception:
        return XML_FILE

def _sigmoid(x):
    return 1.0 / (1.0 + np.exp(-x))

def save_mlp_xml(model, path, layer_sizes):
    """写出 OpenCV ANN_MLP 可读取的 XML 权重文件。"""
    layer_count = len(layer_sizes)

    def format_doubles(weights):
        return ' '.join(('%.16e' % value for value in np.array(weights, dtype=np.float64).flatten()))
    lines = ['<?xml version="1.0"?>', '<opencv_storage>', '<opencv_ml_ann_mlp>', '  <format_version>3</format_version>', '  <layer_sizes>%s</layer_sizes>' % ' '.join(map(str, layer_sizes)), '  <activation_function>SIGMOID_SYM</activation_function>', '  <f_param1>%.17g</f_param1>' % F_PARAM1, '  <f_param2>%.17g</f_param2>' % F_PARAM2, '  <input_scale>%s</input_scale>' % format_doubles(model.getWeights(0)), '  <output_scale>%s</output_scale>' % format_doubles(model.getWeights(layer_count)), '  <inv_output_scale>%s</inv_output_scale>' % format_doubles(model.getWeights(layer_count + 1)), '  <weights>']
    for index in range(1, layer_count):
        lines.append('    <_>%s</_>' % format_doubles(model.getWeights(index)))
    lines += ['  </weights>', '</opencv_ml_ann_mlp>', '</opencv_storage>']
    with open(path, 'w', encoding='utf-8') as stream:
        stream.write('\n'.join(lines))

def _load_model():
    """加载并缓存模型，优先 XML，缺失时回退 PKL 权重。"""
    global _model, _img_size, _load_failed
    if _model is not None:
        return (_model, _img_size)
    if _load_failed:
        return (None, None)
    with _load_lock:
        if _model is not None:
            return (_model, _img_size)
        if _load_failed:
            return (None, None)
        try:
            xml_path = _xml_load_path()
            if xml_path:
                import cv2
                _model = cv2.ml.ANN_MLP_load(xml_path)
                _img_size = (24, 16)
                return (_model, _img_size)
            if not os.path.exists(MODEL_FILE):
                _load_failed = True
                return (None, None)
            with open(MODEL_FILE, 'rb') as stream:
                data = pickle.load(stream)
            _model = data.get('layers', data)
            _img_size = tuple(data['img_size'])
            return (_model, _img_size)
        except Exception as exc:
            _load_failed = True
            print(f'[captcha_ai] 模型加载失败, 本次会话不再重试: {exc}')
            return (None, None)

def predict(img_bgr):
    """返回图片属于验证码弹窗的概率；模型不可用时返回 ``None``。"""
    model, image_size = _load_model()
    if model is None:
        return None
    from PIL import Image
    if len(img_bgr.shape) == 3:
        gray = Image.fromarray(img_bgr[:, :, ::-1]).convert('L')
    else:
        gray = Image.fromarray(img_bgr).convert('L')
    gray = gray.resize(image_size)
    pixels = np.array(gray, dtype=np.float32).flatten() / 255.0
    input_row = pixels.reshape(1, -1).astype(np.float32)
    if not hasattr(model, 'predict'):
        weights = model
        values = input_row.astype(np.float64)
        input_scale = weights.get('input_scale')
        if input_scale is not None:
            input_scale = np.asarray(input_scale, np.float64).flatten()
            values = values * input_scale[0::2] + input_scale[1::2]
        for key in ('w1', 'w2', 'w3'):
            if key not in weights:
                break
            matrix = np.asarray(weights[key], np.float64)
            values = values @ matrix[:-1, :] + matrix[-1, :]
            exponent = np.exp(np.clip(values * -F_PARAM1, -50, 50))
            values = F_PARAM2 * (1.0 - exponent) / (1.0 + exponent)
        output_scale = weights.get('output_scale')
        if output_scale is not None:
            output_scale = np.asarray(output_scale, np.float64).flatten()
            values = values * output_scale[0::2] + output_scale[1::2]
        return float(values[0][0])
    _, output = model.predict(input_row)
    return float(output[0][0])

def is_captcha(img_bgr, threshold=0.5):
    """三态判断：弹窗、非弹窗或模型不可用。"""
    value = predict(img_bgr)
    if value is None:
        return None
    return value > threshold
if __name__ == '__main__':
    import glob
    from ke_engine import SHOT_DIR
    from PIL import Image
    crop_dir = os.path.join(SHOT_DIR, 'crop')
    files = glob.glob(os.path.join(crop_dir, '*.png'))[:5]
    print(f'测试 {len(files)} 张弹窗截图:')
    for filename in files:
        image = Image.open(filename)
        image_bgr = np.array(image.convert('RGB'))[:, :, ::-1].copy()
        score = predict(image_bgr)
        state = '弹窗' if score > 0.5 else '正常'
        print(f'  {os.path.basename(filename)}: {score:.4f} -> {state}')
