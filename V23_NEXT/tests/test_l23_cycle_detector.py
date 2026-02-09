"""
Test V23 — Cycle Detector
"""

from V21_NEXT.l21_memory_core import append_memory_snapshot
from V23_NEXT.l23_cycle_detector import detect_cycle

def test_cycle_detector_basic():
    append_memory_snapshot({
        "raw_value": 0.7,
        "decision_state": "SAFE",
        "entropy": 0.2,
        "is_blackhole": False
    })
    result = detect_cycle(window=10)
    assert result in ("stable_return", "switching", "drifting", "unknown")

