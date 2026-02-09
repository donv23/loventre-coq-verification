"""
Test V22 — Transition Counter
"""

from V21_NEXT.l21_memory_core import append_memory_snapshot
from V22_NEXT.l22_transition_counter import compute_transition_counts

def test_transition_counter_basic():
    # inseriamo una sequenza nota
    append_memory_snapshot({
        "raw_value": 0.5,
        "decision_state": "SAFE",
        "entropy": 0.1,
        "is_blackhole": False
    })
    append_memory_snapshot({
        "raw_value": 0.2,
        "decision_state": "SAFE_ACCESSIBLE",
        "entropy": 0.3,
        "is_blackhole": False
    })
    append_memory_snapshot({
        "raw_value": 0.0,
        "decision_state": "BLACKHOLE",
        "entropy": 0.9,
        "is_blackhole": True
    })

    counts = compute_transition_counts(window=5)
    assert isinstance(counts, dict)
    assert len(counts) >= 1

