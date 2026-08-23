"""使用 OpenCV ANN_MLP 训练验证码弹窗检测模型。"""
from __future__ import annotations
import os
import pickle
import random
import cv2
import numpy as np
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
try:
    from ke_engine import SHOT_DIR
    CAPTCHA_DIR = os.path.join(SHOT_DIR, 'crop')
    NEGATIVE_DIR = os.path.join(SHOT_DIR, 'normal')
except Exception:
    CAPTCHA_DIR = 'C:\\Users\\Administrator\\AppData\\Roaming\\captcha_history'
    NEGATIVE_DIR = os.path.join(SCRIPT_DIR, 'captcha_negatives')
CAPTCHA_CAL_DIR = 'C:\\Users\\Administrator\\AppData\\Roaming\\captcha_calibration'
MODEL_FILE = os.path.join(SCRIPT_DIR, 'captcha_model.pkl')
XML_FILE = os.path.join(SCRIPT_DIR, 'captcha_model.xml')
IMG_SIZE = (24, 16)
REGION_W, REGION_H = (505, 170)

def _imread(path, flags):
    """读取图片，并兼容 OpenCV 不能直接打开的中文路径。"""
    image = cv2.imread(path, flags)
    if image is None:
        try:
            image = cv2.imdecode(np.fromfile(path, dtype=np.uint8), flags)
        except Exception:
            pass
    return image

def _augment(image, n=10):
    """通过随机裁剪与亮度抖动扩充正样本。"""
    augmented = [image]
    height, width = image.shape
    for _ in range(n - 1):
        if width > 4 and height > 3:
            x1 = random.randint(0, max(1, width // 8))
            y1 = random.randint(0, max(1, height // 8))
            x2 = width - random.randint(0, max(1, width // 8))
            y2 = height - random.randint(0, max(1, height // 8))
            crop = image[y1:y2, x1:x2]
            item = cv2.resize(crop, IMG_SIZE)
        else:
            item = image.copy()
        delta = random.randint(-20, 20)
        item = np.clip(item.astype(np.int16) + delta, 0, 255).astype(np.uint8)
        augmented.append(item)
    return augmented

def save_mlp_xml_safe(model, path, layer_sizes):
    """优先调用 OpenCV 原生保存，失败时使用手写 XML。"""
    from captcha_ai import save_mlp_xml
    try:
        model.save(path)
    except Exception as exc:
        print(f'model.save 不可用({str(exc)[:60]}), 手写 XML 序列化...')
        save_mlp_xml(model, path, layer_sizes)

def train_mlp(pos_files=None, neg_files=None, save_dir=None, progress=None):
    """训练模型、保存 XML/PKL，并返回训练集准确率。"""
    save_dir = save_dir or SCRIPT_DIR
    positives = []
    if pos_files is None:
        pos_files = []
        for directory in (CAPTCHA_DIR, CAPTCHA_CAL_DIR):
            if os.path.isdir(directory):
                pos_files += [os.path.join(directory, filename) for filename in os.listdir(directory) if filename.endswith(('.png', '.jpg'))]
    for filename in pos_files:
        try:
            image = _imread(filename, cv2.IMREAD_GRAYSCALE)
            if image is not None:
                positives.append(cv2.resize(image, IMG_SIZE))
        except Exception:
            continue
    if not positives:
        raise ValueError('正样本不足(弹窗截图)')
    if neg_files is None:
        neg_files = glob_all(NEGATIVE_DIR)
    negatives = []
    random_files = list(neg_files)
    random.shuffle(random_files)
    for filename in random_files:
        try:
            image = _imread(filename, cv2.IMREAD_GRAYSCALE)
            if image is None:
                continue
            height, width = image.shape
            if width > REGION_W and height > REGION_H:
                x1 = random.randint(0, width - REGION_W)
                y1 = random.randint(0, height - REGION_H)
                crop = image[y1:y1 + REGION_H, x1:x1 + REGION_W]
                negatives.append(cv2.resize(crop, IMG_SIZE))
        except Exception:
            continue
    if not negatives:
        raise ValueError('负样本不足(正常画面)')
    negative_count = min(len(positives) * 10, len(negatives))
    negatives = negatives[:negative_count]
    if progress:
        progress(0)
    train_data = []
    train_labels = []
    for image in positives:
        for augmented in _augment(image):
            train_data.append(augmented.flatten().astype(np.float32) / 255.0)
            train_labels.append([1.0])
    for image in negatives:
        train_data.append(image.flatten().astype(np.float32) / 255.0)
        train_labels.append([0.0])
    inputs = np.array(train_data, dtype=np.float32)
    labels = np.array(train_labels, dtype=np.float32)
    if progress:
        progress(1)
    model = cv2.ml.ANN_MLP_create()
    layer_sizes = np.array([inputs.shape[1], 64, 32, 1], dtype=np.int32)
    model.setLayerSizes(layer_sizes)
    model.setActivationFunction(cv2.ml.ANN_MLP_SIGMOID_SYM)
    model.setTrainMethod(cv2.ml.ANN_MLP_BACKPROP, 0.01, 0.01)
    model.setTermCriteria((cv2.TERM_CRITERIA_COUNT | cv2.TERM_CRITERIA_EPS, 1000, 0.0001))
    model.train(inputs, cv2.ml.ROW_SAMPLE, labels)
    if progress:
        progress(2)
    _, outputs = model.predict(inputs)
    accuracy = float(np.mean((outputs.ravel() > 0.5).astype(np.float32) == labels.ravel()))
    save_mlp_xml_safe(model, os.path.join(save_dir, 'captcha_model.xml'), layer_sizes.tolist())
    weights = {'w1': model.getWeights(1), 'w2': model.getWeights(2), 'w3': model.getWeights(3), 'input_scale': model.getWeights(0), 'output_scale': model.getWeights(len(layer_sizes)), 'inv_output_scale': model.getWeights(len(layer_sizes) + 1), 'img_size': IMG_SIZE}
    with open(os.path.join(save_dir, 'captcha_model.pkl'), 'wb') as stream:
        pickle.dump(weights, stream)
    if progress:
        progress(3)
    return accuracy

def glob_all(directory):
    if not os.path.isdir(directory):
        return []
    return [os.path.join(directory, filename) for filename in os.listdir(directory) if filename.endswith(('.png', '.jpg'))]
if __name__ == '__main__':
    accuracy = train_mlp(progress=lambda stage: print(f'阶段 {stage + 1}/4'))
    print(f'训练完成, 准确率: {accuracy * 100:.1f}%')
    first_positive = None
    for filename in glob_all(CAPTCHA_DIR):
        image = _imread(filename, cv2.IMREAD_GRAYSCALE)
        if image is not None:
            first_positive = image
            break
    if first_positive is not None:
        input_row = cv2.resize(first_positive, IMG_SIZE).flatten().astype(np.float32) / 255.0
        loaded = cv2.ml.ANN_MLP_load(os.path.join(SCRIPT_DIR, 'captcha_model.xml'))
        value = loaded.predict(input_row.reshape(1, -1))[1][0][0]
        print(f'自检: 弹窗截图预测 {value:.3f}')
