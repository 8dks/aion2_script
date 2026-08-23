"""永久版的离线数据收集兼容层。

原模块会把验证码样本、共享学习事件和训练请求发送到授权服务器。永久版
关闭这些远程能力，但保留函数签名，避免旧调用点报错。
"""

from __future__ import annotations


VERSION = "v26.8.21-permanent"
TRAIN_STAT = None


def upload_once(_base, _key="", _hwid=""):
    return 0


def _upload_events(_base, _key="", _hwid=""):
    return 0


def _fetch_shared_table(_base, _key="", _hwid=""):
    return 0


def fetch_train_stat(_key="", _hwid=""):
    return None


def fetch_train_data(_key, _hwid, _save_dir, _fp_file):
    raise RuntimeError("永久版已关闭原授权服务器的云端训练数据")


def start_collector(_settings_getter):
    return None
