"""Shared helpers for the derived-case modules (cases_*.py)."""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def registry():
    cases = []

    def case(cid, cite):
        def deco(fn):
            cases.append((cid, cite, fn))
            return fn
        return deco

    return cases, case


def rejects(fn, *args, exc, **kw):
    try:
        fn(*args, **kw)
    except exc as e:
        return e
    raise AssertionError(f"accepted; expected {getattr(exc, '__name__', exc)}")


def accepts(fn, *args, **kw):
    try:
        return fn(*args, **kw)
    except Exception as e:  # noqa: BLE001
        raise AssertionError(f"refused unexpectedly: {type(e).__name__}: {e}")


def put(buf, offset, value):
    b = bytearray(buf)
    if isinstance(value, int):
        b[offset] = value
    else:
        b[offset:offset + len(value)] = value
    return bytes(b)


def flip(buf, offset, mask=0x01):
    b = bytearray(buf)
    b[offset] ^= mask
    return bytes(b)
