"""
Test V21 — memory core
"""
import os
import json

from V21_NEXT.l21_memory_core import (
    ensure_memory_ready,
    append_memory_snapshot,
    tail_memory,
)

def test_memory_core_basic():
    # prepara file
    path = ensure_memory_ready()
    assert os.path.exists(path)

    # aggiungi un record fittizio
    snap = append_memory_snapshot({
        "raw_value": 0.42,
        "decision_state": "SAFE",
        "entropy": 0.11,
        "is_blackhole": False
    })
    assert "timestamp" in snap
    assert snap["raw_value"] == 0.42

    # recupera coda
    tail = tail_memory(5)
    assert isinstance(tail, list)
    assert len(tail) >= 1
    x = tail[-1]
    assert x["decision"] == "SAFE"

