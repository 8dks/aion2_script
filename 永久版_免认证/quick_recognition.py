"""快速颜色与模板识别服务。"""
from __future__ import annotations
import time
import cv2
import numpy as np
DEFAULT_H_TOL = 12
DEFAULT_S_TOL = 60
DEFAULT_V_TOL = 80
DEFAULT_TOLERANCE = 25
MIN_PIXEL_RATIO = 0.03
AUX_POINT_HIT_RATIO = 0.6

class QuickRecognition:
    """使用屏幕捕获对象完成快速颜色和图像识别。"""

    def __init__(self, screen=None, dd=None):
        self.scr = screen
        self.dd = dd
        self._mode = 'screen'
        self._main_win = None

    def runQuickColorPick(self, cfg):
        if self.scr is None:
            return None
        __temp_2, __temp_3 = self._get_frame()
        full = __temp_2
        r = __temp_3
        if full is None:
            return None
        wh = r[3] - r[1]
        ww = r[2] - r[0]
        __temp_5, __temp_6, __temp_7, __temp_8 = self._cfg_region(cfg, r)
        x = __temp_5
        y = __temp_6
        w = __temp_7
        h = __temp_8
        h = max(1, h)
        w = max(1, w)
        t_raw = cfg.get('color')
        if t_raw is None:
            return None
        target = np.array(t_raw, dtype=np.uint8)
        _ey = min(full.shape[0], y - r[1] + h)
        _sy = max(0, y - r[1])
        _ex = min(full.shape[1], x - r[0] + w)
        _sx = max(0, x - r[0])
        img = full[slice(_sy, _ey), slice(_sx, _ex)]
        if img.size == 0:
            return None
        use_hsv = cfg.get('hsv', False)
        if use_hsv:
            __temp_22, __temp_23, __temp_24 = self._hsv_match(img, target, cfg.get('h_tol', DEFAULT_H_TOL), cfg.get('s_tol', DEFAULT_S_TOL), cfg.get('v_tol', DEFAULT_V_TOL))
            cnt = __temp_22
            total = __temp_23
            mask = __temp_24
        else:
            target_bgr = target[slice(None, None, -1)]
            tol = cfg.get('tolerance', DEFAULT_TOLERANCE)
            diff = np.abs(img.astype(np.int16) - target_bgr)
            mask = np.all(diff <= tol, axis=2)
            cnt = int(np.count_nonzero(mask))
            total = mask.size
        min_px = max(2, int(total * MIN_PIXEL_RATIO))
        if cnt < min_px:
            return None
        __temp_34, __temp_35 = np.where(mask)
        ys = __temp_34
        xs = __temp_35
        cx = _sx + int(xs.mean())
        cy = _sy + int(ys.mean())
        return (round(cx / ww * 100, 2), round(cy / wh * 100, 2))

    def runQuickColorRegionPick(self, cfg):
        if self.scr is None:
            return None
        __temp_43, __temp_44 = self._get_frame()
        full = __temp_43
        r = __temp_44
        if full is None:
            return None
        wh = r[3] - r[1]
        ww = r[2] - r[0]
        __temp_46, __temp_47, __temp_48, __temp_49 = self._cfg_region(cfg, r)
        x = __temp_46
        y = __temp_47
        w = __temp_48
        h = __temp_49
        t_raw = cfg.get('color')
        if t_raw is None:
            return None
        target = np.array(t_raw, dtype=np.uint8)
        _ey = min(full.shape[0], y - r[1] + h)
        _sy = max(0, y - r[1])
        _ex = min(full.shape[1], x - r[0] + w)
        _sx = max(0, x - r[0])
        img = full[slice(_sy, _ey), slice(_sx, _ex)]
        if img.size == 0:
            return None
        use_hsv = cfg.get('hsv', False)
        if use_hsv:
            __temp_61, __temp_62, __temp_63 = self._hsv_match(img, target, cfg.get('h_tol', DEFAULT_H_TOL), cfg.get('s_tol', DEFAULT_S_TOL), cfg.get('v_tol', DEFAULT_V_TOL))
            cnt = __temp_61
            total = __temp_62
            mask = __temp_63
        else:
            target_bgr = target[slice(None, None, -1)]
            tol = cfg.get('tolerance', DEFAULT_TOLERANCE)
            diff = np.abs(img.astype(np.int16) - target_bgr)
            mask = np.all(diff <= tol, axis=2)
            cnt = int(np.count_nonzero(mask))
            total = mask.size
        pts = cfg.get('points', None)
        if pts:
            if len(pts) > 0:
                pts_hit = 0
                for __temp_72 in iter(pts):
                    pt = __temp_72
                    _pc = pt.get('color')
                    if _pc is None:
                        continue
                    px, py, pw, ph = self._cfg_region(pt, r)
                    pc = np.array(_pc, dtype=np.uint8)
                    _pey = min(full.shape[0], py - r[1] + ph)
                    _psy = max(0, py - r[1])
                    _pex = min(full.shape[1], px - r[0] + pw)
                    _psx = max(0, px - r[0])
                    pimg = full[slice(_psy, _pey), slice(_psx, _pex)]
                    if pimg.size == 0:
                        continue
                    if use_hsv:
                        phsv = cv2.cvtColor(pimg, cv2.COLOR_BGR2HSV)
                        pt_hsv = cv2.cvtColor(pc[slice(None, None, -1)].reshape(1, 1, 3).astype(np.uint8), cv2.COLOR_BGR2HSV)[0, 0]
                        pdiff = np.abs(phsv.astype(int) - pt_hsv.astype(int))
                        if np.count_nonzero(np.all(pdiff <= [DEFAULT_H_TOL, DEFAULT_S_TOL, DEFAULT_V_TOL], axis=2)) >= 1:
                            pts_hit += 1
                        continue
                    pcb = pc[slice(None, None, -1)]
                    ptol = pt.get('tolerance', pt.get('tol', tol))
                    pdiff = np.abs(pimg.astype(np.int16) - pcb)
                    if np.count_nonzero(np.all(pdiff <= ptol, axis=2)) >= 1:
                        pts_hit += 1
                    continue
                if pts_hit < max(1, len(pts) * AUX_POINT_HIT_RATIO):
                    return None
        min_px = max(2, int(total * MIN_PIXEL_RATIO))
        if cnt < min_px:
            return None
        __temp_110, __temp_111 = np.where(mask)
        ys = __temp_110
        xs = __temp_111
        cx = _sx + int(xs.mean())
        cy = _sy + int(ys.mean())
        return (round(cx / ww * 100, 2), round(cy / wh * 100, 2))

    def runQuickRecognition(self, cfg, template_img):
        if self.scr is not None:
            if template_img is None:
                return None
        else:
            return None
        __temp_119, __temp_120 = self._get_frame()
        full = __temp_119
        r = __temp_120
        if full is None:
            return None
        wh = r[3] - r[1]
        ww = r[2] - r[0]
        __temp_122, __temp_123, __temp_124, __temp_125 = self._cfg_region(cfg, r)
        x = __temp_122
        y = __temp_123
        w = __temp_124
        h = __temp_125
        _ey = min(full.shape[0], y - r[1] + h)
        _sy = max(0, y - r[1])
        _ex = min(full.shape[1], x - r[0] + w)
        _sx = max(0, x - r[0])
        roi = full[slice(_sy, _ey), slice(_sx, _ex)]
        if roi.size == 0:
            return None
        threshold = cfg.get('threshold', 0.8)
        result = cv2.matchTemplate(roi, template_img, cv2.TM_CCOEFF_NORMED)
        __temp_133, __temp_134, __temp_135, __temp_136 = cv2.minMaxLoc(result)
        _ = __temp_133
        max_val = __temp_134
        _ = __temp_135
        max_loc = __temp_136
        if not max_val != max_val:
            if max_val < threshold:
                return None
        else:
            return None
        cx = _sx + max_loc[0] + template_img.shape[1] // 2
        cy = _sy + max_loc[1] + template_img.shape[0] // 2
        return (round(cx / ww * 100, 2), round(cy / wh * 100, 2), round(float(max_val), 3))

    def runQuickImageCapture(self, cfg):
        if self.scr is None:
            return None
        __temp_142, __temp_143 = self._get_frame()
        full = __temp_142
        r = __temp_143
        if full is None:
            return None
        __temp_145, __temp_146, __temp_147, __temp_148 = self._cfg_region(cfg, r)
        x = __temp_145
        y = __temp_146
        w = __temp_147
        h = __temp_148
        if not w < 1:
            if h < 1:
                return None
        else:
            return None
        _ey = min(full.shape[0], y - r[1] + h)
        _sy = max(0, y - r[1])
        _ex = min(full.shape[1], x - r[0] + w)
        _sx = max(0, x - r[0])
        if not _ex <= _sx:
            if _ey <= _sy:
                return None
        else:
            return None
        return full[slice(_sy, _ey), slice(_sx, _ex)].copy()

    def runQuickPercentRegionPick(self, cfg):
        return (cfg.get('x_pct', 0), cfg.get('y_pct', 0), cfg.get('w_pct', 1), cfg.get('h_pct', 1))

    def clearCaptureLoadingWindow(self, *args):
        return None

    def getRecognitionCaptureMode(self):
        return self._mode

    def syncCaptureMainWindowRefs(self, win):
        self._main_win = win

    def _get_frame(self):
        rect = self.scr.rect()
        full = self.scr.grab((rect[0], rect[1], rect[2], rect[3]))
        return (full, rect)

    def _cfg_region(self, cfg, rect):
        x_percent = cfg.get('x_pct', 0)
        y_percent = cfg.get('y_pct', 0)
        width_percent = cfg.get('w_pct', 1)
        height_percent = cfg.get('h_pct', 1)
        window_width = rect[2] - rect[0]
        window_height = rect[3] - rect[1]
        x = rect[0] + int(window_width * x_percent / 100)
        y = rect[1] + int(window_height * y_percent / 100)
        width = max(1, int(window_width * width_percent / 100))
        height = max(1, int(window_height * height_percent / 100))
        return (x, y, width, height)

    def _hsv_match(self, img_bgr, target_rgb, h_tol=12, s_tol=60, v_tol=80, min_v=0, min_blob=8):
        target_bgr = np.array(target_rgb[::-1], dtype=np.uint8).reshape(1, 1, 3)
        pixel_hsv = cv2.cvtColor(img_bgr, cv2.COLOR_BGR2HSV)
        target_hsv = cv2.cvtColor(target_bgr, cv2.COLOR_BGR2HSV)[0, 0]
        hue, saturation, value = (int(target_hsv[0]), int(target_hsv[1]), int(target_hsv[2]))
        if value < 40:
            hue_low, hue_high = (0, 180)
            s_tol = min(s_tol, 30)
        elif value < 80:
            hue_low = (hue - max(h_tol, 30)) % 180
            hue_high = (hue + max(h_tol, 30)) % 180
        else:
            hue_low = (hue - h_tol) % 180
            hue_high = (hue + h_tol) % 180
        lower = np.array([min(hue_low, hue_high), max(0, saturation - s_tol), max(0, value - v_tol)], dtype=np.uint8)
        upper = np.array([max(hue_low, hue_high), min(255, saturation + s_tol), min(255, value + v_tol)], dtype=np.uint8)
        if hue_low <= hue_high:
            mask = cv2.inRange(pixel_hsv, lower, upper)
        else:
            high_range = cv2.inRange(pixel_hsv, np.array([hue_low, lower[1], lower[2]], dtype=np.uint8), np.array([180, upper[1], upper[2]], dtype=np.uint8))
            low_range = cv2.inRange(pixel_hsv, np.array([0, lower[1], lower[2]], dtype=np.uint8), np.array([hue_high, upper[1], upper[2]], dtype=np.uint8))
            mask = cv2.bitwise_or(high_range, low_range)
        if min_v > 0:
            value_mask = cv2.inRange(pixel_hsv, np.array([0, 0, min_v]), np.array([180, 255, 255]))
            mask = cv2.bitwise_and(mask, value_mask)
        count = cv2.countNonZero(mask) if len(mask.shape) == 2 else 0
        if min_blob > 0 and count > 0 and (len(mask.shape) == 2):
            if count < min_blob:
                return (0, mask.size, mask)
            min_blob = min(min_blob, mask.size)
            _components, labels, _stats, _centroids = cv2.connectedComponentsWithStats(mask)
            counts = np.bincount(labels.ravel())
            big = counts >= min_blob
            big[0] = False
            mask = big[labels].astype(np.uint8) * 255 if np.any(big) else np.zeros_like(mask)
            count = cv2.countNonZero(mask)
        return (count, mask.size, mask)
