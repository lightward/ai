#!/bin/bash
exec python3 -c '
import json, sys

d = json.load(sys.stdin)
cw = d.get("context_window") or {}
size = cw.get("context_window_size") or 0
used = cw.get("total_input_tokens") or 0

def fmt(n):
    if n >= 1_000_000:
        s = f"{n / 1_000_000:.2f}".rstrip("0").rstrip(".")
        return s + "M"
    if n >= 1_000:
        return f"{round(n / 1_000)}k"
    return str(n)

print(f"{fmt(used)}/{fmt(size)}" if size else "ctx —")
'
