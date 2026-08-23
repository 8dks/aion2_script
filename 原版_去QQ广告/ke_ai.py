"""KE AI：文字检测、角度矫正与小地图目标检测。"""
from __future__ import annotations
import os
import sys
import threading
import traceback
import cv2
import numpy as np
def _find_model_dir():
    candidates = []
    if getattr(sys, '_MEIPASS', None):
        candidates += [
            os.path.dirname(os.path.abspath(sys.argv[0])),
            getattr(sys, '_MEIPASS', None),
        ]
    candidates.append(os.path.dirname(os.path.abspath(__file__)))
    for directory in candidates:
        model_dir = os.path.join(directory, 'models')
        if os.path.isdir(model_dir):
            return model_dir
    return os.path.join(candidates[0], 'models')

MODEL_DIR = _find_model_dir()
_AI_LOCK = threading.Lock()
_ocr_det = None
_ocr_ang = None
_minimap = None

def ocr_detect_text(img_bgr):
    """检测图片中的文字区域，返回包含全部文字的裁剪图。"""
    global _ocr_det
    try:
        if _ocr_det is None:
            with _AI_LOCK:
                if _ocr_det is None:
                    import onnxruntime as ort
                    model_path = os.path.join(MODEL_DIR, 'ocr_det.onnx')
                    if not os.path.exists(model_path):
                        return None
                    _ocr_det = ort.InferenceSession(model_path, providers=['CPUExecutionProvider'])
        height, width = img_bgr.shape[:2]
        ratio = 1.0
        if max(height, width) > 960:
            ratio = 960 / max(height, width)
            resized_height = int(height * ratio)
            resized_width = int(width * ratio)
            image = cv2.resize(img_bgr, (resized_width, resized_height))
        else:
            image = img_bgr.copy()
            resized_height, resized_width = (height, width)
        pad_height = (32 - resized_height % 32) % 32
        pad_width = (32 - resized_width % 32) % 32
        if pad_height or pad_width:
            image = cv2.copyMakeBorder(image, 0, pad_height, 0, pad_width, cv2.BORDER_CONSTANT, value=(0, 0, 0))
        input_tensor = image.astype(np.float32) / 255.0
        input_tensor = (input_tensor - 0.5) / 0.5
        input_tensor = input_tensor.transpose(2, 0, 1)[np.newaxis, ...].astype(np.float32)
        output = _ocr_det.run(None, {_ocr_det.get_inputs()[0].name: input_tensor})[0]
        mask = (output[0, 0] > 0.3).astype(np.uint8) * 255
        contours, _ = cv2.findContours(mask, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
        if not contours:
            return None
        min_x, min_y = (resized_width, resized_height)
        max_x, max_y = (0, 0)
        for contour in contours:
            x, y, box_width, box_height = cv2.boundingRect(contour)
            if box_width < 5 or box_height < 5:
                continue
            min_x, min_y = (min(min_x, x), min(min_y, y))
            max_x, max_y = (max(max_x, x + box_width), max(max_y, y + box_height))
        if max_x <= min_x or max_y <= min_y:
            return None
        min_x, min_y = (int(min_x / ratio), int(min_y / ratio))
        max_x, max_y = (int(max_x / ratio), int(max_y / ratio))
        return img_bgr[max(0, min_y - 2):min(height, max_y + 2), max(0, min_x - 2):min(width, max_x + 2)]
    except Exception as exc:
        print(f'[AI.ocr_detect_text] {exc}\n{traceback.format_exc()}')
        return None

def ocr_correct_angle(img_bgr):
    """根据角度模型矫正文字倾斜。"""
    global _ocr_ang
    try:
        if _ocr_ang is None:
            with _AI_LOCK:
                if _ocr_ang is None:
                    import onnxruntime as ort
                    model_path = os.path.join(MODEL_DIR, 'ocr_angle.onnx')
                    if not os.path.exists(model_path):
                        return img_bgr
                    _ocr_ang = ort.InferenceSession(model_path, providers=['CPUExecutionProvider'])
        height, width = img_bgr.shape[:2]
        image = cv2.resize(img_bgr, (224, 224))
        input_tensor = image.astype(np.float32) / 255.0
        input_tensor = (input_tensor - 0.5) / 0.5
        input_tensor = input_tensor.transpose(2, 0, 1)[np.newaxis, ...].astype(np.float32)
        angle = float(_ocr_ang.run(None, {_ocr_ang.get_inputs()[0].name: input_tensor})[0][0, 0])
        if abs(angle) < 0.5:
            return img_bgr
        matrix = cv2.getRotationMatrix2D((width / 2, height / 2), angle, 1.0)
        return cv2.warpAffine(img_bgr, matrix, (width, height), borderMode=cv2.BORDER_REPLICATE)
    except Exception as exc:
        print(f'[AI.ocr_correct_angle] {exc}\n{traceback.format_exc()}')
        return img_bgr

def _iou(a, b):
    x1 = max(a[0], b[0])
    y1 = max(a[1], b[1])
    x2 = min(a[2], b[2])
    y2 = min(a[3], b[3])
    intersection = max(0, x2 - x1) * max(0, y2 - y1)
    area_a = (a[2] - a[0]) * (a[3] - a[1])
    area_b = (b[2] - b[0]) * (b[3] - b[1])
    return intersection / (area_a + area_b - intersection + 1e-06)

def minimap_detect(img_bgr):
    """扫描小地图，返回 ``(x1, y1, x2, y2, confidence)`` 列表。"""
    global _minimap
    try:
        if _minimap is None:
            with _AI_LOCK:
                if _minimap is None:
                    import onnxruntime as ort
                    model_path = os.path.join(MODEL_DIR, 'minimap_yolo.onnx')
                    if not os.path.exists(model_path):
                        return []
                    _minimap = ort.InferenceSession(model_path, providers=['CPUExecutionProvider'])
        image = cv2.cvtColor(img_bgr, cv2.COLOR_BGR2RGB)
        image = cv2.resize(image, (640, 640))
        image = image.astype(np.float32) / 255.0
        image = image.transpose(2, 0, 1)[np.newaxis, ...].astype(np.float32)
        prediction = _minimap.run(None, {'images': image})[0][0]
        boxes = []
        for index in range(prediction.shape[1]):
            x, y, width, height = (prediction[0, index], prediction[1, index], prediction[2, index], prediction[3, index])
            confidence = float(prediction[4, index])
            if confidence > 0.15:
                x1 = max(0, int(x - width / 2))
                y1 = max(0, int(y - height / 2))
                x2 = min(640, int(x + width / 2))
                y2 = min(640, int(y + height / 2))
                if x2 > x1 and y2 > y1:
                    boxes.append((x1, y1, x2, y2, confidence))
        if len(boxes) > 1:
            boxes.sort(key=lambda box: box[4], reverse=True)
            kept = []
            while boxes:
                kept.append(boxes[0])
                boxes = [box for box in boxes[1:] if _iou(box, boxes[0]) < 0.5]
            boxes = kept
        height, width = img_bgr.shape[:2]
        scale_x, scale_y = (width / 640, height / 640)
        return [(int(x1 * scale_x), int(y1 * scale_y), int(x2 * scale_x), int(y2 * scale_y), confidence) for x1, y1, x2, y2, confidence in boxes]
    except Exception as exc:
        print(f'[minimap] {exc}')
        return []
