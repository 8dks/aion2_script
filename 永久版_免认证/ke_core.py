"""永久版的本地授权兼容层。

保留原模块公开函数，供旧调用点兼容；所有结果均在本地生成，不读取硬件
指纹、激活缓存，也不会建立网络连接。
"""

from __future__ import annotations


LICENSE_TYPE = "永久版"
LICENSE_EXPIRES = "永久"

_act_key = "LOCAL-PERMANENT"
_act_hwid = ""
_act_type = LICENSE_TYPE
_act_exp = LICENSE_EXPIRES
_act_ok = True


def verify_resp(_resp, _key, _hwid):
    """兼容原响应校验入口；永久版始终使用本地授权状态。"""
    return True


def write_act_cache(_cache_file, _resp, _key, _hwid):
    """永久版不写激活缓存。"""
    return True


def read_act_cache(_cache_file, _key, _hwid):
    """返回本地永久授权状态。"""
    return LICENSE_TYPE, LICENSE_EXPIRES, True


def init_activation(settings=None):
    """初始化本地永久授权，并返回兼容的确认函数。"""
    if isinstance(settings, dict):
        settings.update(
            {
                "activate_key": _act_key,
                "activate_type": LICENSE_TYPE,
                "activate_exp": LICENSE_EXPIRES,
                "is_admin": True,
            }
        )
    return lambda: True
