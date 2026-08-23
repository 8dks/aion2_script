import heapq
import math
import os
import sys
import threading

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


DEFAULT_MODEL = _find_model('captcha_ocr.onnx')
CHARSET = '023456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
CONFIDENCE_MIN = 0.7


class CaptchaOcr:
    def __init__(self, model_path=DEFAULT_MODEL):
        if not os.path.exists(model_path):
            raise FileNotFoundError(f'识别模型不存在: {model_path}')
        self._sess = ort.InferenceSession(model_path, providers=['CPUExecutionProvider'])
        self._lock = threading.Lock()
        inp = self._sess.get_inputs()[0]
        assert list(inp.shape[1:]) == [3, 99, 301], f'模型输入异常: {inp.shape}'
        out = self._sess.get_outputs()[0]
        assert list(out.shape[1:]) == [5, 61], f'模型输出异常: {out.shape}, 预期 [*,5,61]'

    def _prob(self, frame_bgr, box, roi=None):
        if roi is None:
            x1, y1, x2, y2 = (int(value) for value in box)
            height, width = frame_bgr.shape[:2]
            x1, y1 = max(0, x1), max(0, y1)
            x2, y2 = min(width, x2), min(height, y2)
            if x2 <= x1 or y2 <= y1:
                return None
            box_width, box_height = x2 - x1, y2 - y1
            crop_x1 = x1 + int(box_width * 0.01)
            crop_x2 = x1 + int(box_width * 0.99)
            crop_y1 = y1 + int(box_height * 0.115)
            crop_y2 = y1 + int(box_height * 0.92)
            roi = frame_bgr[crop_y1:crop_y2, crop_x1:crop_x2]
            if roi.size == 0:
                return None
        gray = cv2.cvtColor(roi, cv2.COLOR_BGR2GRAY)
        _, binary = cv2.threshold(gray, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
        tile = cv2.resize(binary, (301, 99), interpolation=cv2.INTER_LANCZOS4)
        blob = np.stack([tile] * 3, axis=-1).astype(np.float32) / 255.0
        blob = np.transpose(blob, (2, 0, 1))[None]
        with self._lock:
            logits = self._sess.run(None, {'input': blob})[0][0]
        values = np.exp(logits - logits.max(-1, keepdims=True))
        return values / values.sum(-1, keepdims=True)

    def recognize(self, frame_bgr, box, roi=None):
        try:
            probability = self._prob(frame_bgr, box, roi)
            if probability is None:
                return None, 0
            answer = ''.join(CHARSET[index] for index in probability.argmax(-1))
            confidence = float(probability.max(-1).prod())
            if confidence < CONFIDENCE_MIN:
                return None, confidence
            return answer, confidence
        except Exception as exc:
            import traceback
            print(f'[CaptchaOcr.recognize] 异常: {exc} {traceback.format_exc()}')
            return None, 0

    def topk_answers(self, frame_bgr, box, roi=None, k=3):
        try:
            probability = self._prob(frame_bgr, box, roi)
            if probability is None:
                return []
            beam = [(0.0, '')]
            for position in range(5):
                next_beam = []
                for log_probability, prefix in beam:
                    for character_index in range(61):
                        value = float(probability[position, character_index])
                        if value > 0:
                            next_beam.append(
                                (
                                    log_probability + math.log(value),
                                    prefix + CHARSET[character_index],
                                )
                            )
                beam = heapq.nlargest(k, next_beam) if next_beam else beam
            seen = {}
            for log_probability, answer in beam:
                if answer not in seen or log_probability > seen[answer][0]:
                    seen[answer] = (log_probability, answer)
            ordered = sorted(seen.values(), key=lambda item: -item[0])[:k]
            return [(answer, math.exp(log_probability)) for log_probability, answer in ordered]
        except Exception as exc:
            import traceback
            print(f'[CaptchaOcr.topk_answers] 异常: {exc} {traceback.format_exc()}')
            return []
