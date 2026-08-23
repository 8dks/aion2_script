"""验证码 YOLO 定位器。"""
from __future__ import annotations
import os
import sys
import threading
import traceback
import cv2
import numpy as np
import onnxruntime as ort
def _find_model(name):
    candidates = []
    if getattr(sys, '_MEIPASS', None):
        candidates += [
            os.path.dirname(os.path.abspath(sys.argv[0])),
            getattr(sys, '_MEIPASS', None),
        ]
    candidates.append(os.path.dirname(os.path.abspath(__file__)))
    for directory in candidates:
        model_path = os.path.join(directory, 'models', name)
        if os.path.exists(model_path):
            return model_path
    return os.path.join(candidates[0], 'models', name)

DEFAULT_MODEL = _find_model('captcha_presence_yolov5.onnx')
_SCALES = ((80, 8), (40, 16), (20, 32))
_CLS_NAMES = {0: 'captcha', 1: 'input', 2: 'confirm'}

class YoloCaptchaLocator:
    """从全屏 BGR 帧中检测验证码弹窗、输入框与确认按钮。"""

    def __init__(self, model_path=DEFAULT_MODEL, conf_thresh=0.5, iou_thresh=0.45):
        if not os.path.exists(model_path):
            raise FileNotFoundError(f'模型文件不存在: {model_path}')
        self._sess = ort.InferenceSession(model_path, providers=['CPUExecutionProvider'])
        self._conf = conf_thresh
        self._iou = iou_thresh
        self._lock = threading.Lock()
        inp = self._sess.get_inputs()[0]
        assert inp.shape[2:] == [640, 640], f'模型输入异常: {inp.shape}'
        out = self._sess.get_outputs()[0]
        assert list(out.shape) == [1, 25200, 8], f'模型输出异常: {out.shape}'

    def locate(self, frame_bgr):
        """返回各目标在原图中的像素坐标字典；未检测到时返回 ``None``。"""
        try:
            with self._lock:
                boxes = self._infer(frame_bgr)
        except Exception:
            print(f'[captcha_yolo] 推理异常:\n{traceback.format_exc()}')
            return None
        if not boxes:
            return None
        result = {}
        for cls_id, _score, x1, y1, x2, y2 in boxes:
            key = _CLS_NAMES.get(cls_id)
            if key and key not in result:
                result[key] = (x1, y1, x2, y2)
        return result or None

    def _infer(self, frame_bgr):
        __temp_1657, __temp_1658 = frame_bgr.shape[slice(None, 2)]
        H = __temp_1657
        W = __temp_1658
        __temp_1660, __temp_1661, __temp_1662, __temp_1663 = self._letterbox(frame_bgr, 640)
        canvas = __temp_1660
        ox = __temp_1661
        oy = __temp_1662
        scale = __temp_1663
        blob = cv2.cvtColor(canvas, cv2.COLOR_BGR2RGB).astype(np.float32) / 255.0
        blob = np.transpose(blob, (2, 0, 1))[None]
        pred = self._sess.run(None, {'images': blob})[0][0]
        cls_ids = []
        scores = []
        boxes = []
        offset = 0
        for __temp_1672 in iter(_SCALES):
            __temp_1673, __temp_1674 = __temp_1672
            G = __temp_1673
            _stride = __temp_1674
            seg = pred[slice(offset, offset + G * G * 3)]
            offset += G * G * 3
            seg = seg.reshape(3, G, G, 8)
            obj = seg[Ellipsis, 4]
            cl = seg[Ellipsis, slice(5, 8)]
            score = obj * cl.max(-1)
            mask = score > self._conf
            for __temp_1678 in iter(range(3)):
                a = __temp_1678
                __temp_1680, __temp_1681 = np.nonzero(mask[a])
                ys = __temp_1680
                xs = __temp_1681
                if not len(ys):
                    continue
                for __temp_1687 in range(len(ys)):
                    i = __temp_1687
                    __temp_1688, __temp_1689 = seg[a][ys[i], xs[i], slice(0, 2)]
                    cx = __temp_1688
                    cy = __temp_1689
                    __temp_1690, __temp_1691 = seg[a][ys[i], xs[i], slice(2, 4)]
                    w = __temp_1690
                    h = __temp_1691
                    boxes.append([cx - w / 2, cy - h / 2, cx + w / 2, cy + h / 2])
                    scores.append(float(score[a][ys[i], xs[i]]))
                    cls_ids.append(int(cl[a][ys[i], xs[i]].argmax()))
                    continue
                continue
            continue
        if not boxes:
            return []
        boxes = np.array(boxes)
        boxes_xywh = np.column_stack([boxes[slice(None, None), 0], boxes[slice(None, None), 1], boxes[slice(None, None), 2] - boxes[slice(None, None), 0], boxes[slice(None, None), 3] - boxes[slice(None, None), 1]])
        keep = cv2.dnn.NMSBoxes(boxes_xywh.tolist(), scores, self._conf, self._iou)
        results = []
        for __temp_1707 in iter(keep.flatten()):
            i = __temp_1707
            __temp_1708, __temp_1709, __temp_1710, __temp_1711 = boxes[i]
            x1 = __temp_1708
            y1 = __temp_1709
            x2 = __temp_1710
            y2 = __temp_1711
            results.append((cls_ids[i], scores[i], int((x1 - ox) / scale), int((y1 - oy) / scale), int((x2 - ox) / scale), int((y2 - oy) / scale)))
            continue
        return results

    @staticmethod
    def _letterbox(image, size=640):
        """等比缩放并用灰色填边，返回画布、偏移与缩放比例。"""
        height, width = image.shape[:2]
        scale = size / max(height, width)
        new_width = max(1, int(width * scale))
        new_height = max(1, int(height * scale))
        resized = cv2.resize(image, (new_width, new_height))
        canvas = np.full((size, size, 3), 114, dtype=np.uint8)
        offset_x = (size - new_width) // 2
        offset_y = (size - new_height) // 2
        canvas[offset_y:offset_y + new_height, offset_x:offset_x + new_width] = resized
        return (canvas, offset_x, offset_y, scale)
