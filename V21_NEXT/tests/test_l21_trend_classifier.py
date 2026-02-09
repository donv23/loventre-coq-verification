"""
Test V21 — trend classifier
"""
from V21_NEXT.l21_memory_core import append_memory_snapshot
from V21_NEXT.l21_trend_classifier import classify_trend

def test_trend_classifier_basic():
    # crea alcuni record noti
    append_memory_snapshot({
        "raw_value": 0.1,
        "decision_state": "SAFE",
        "entropy": 0.0,
        "is_blackhole": False
    })
    append_memory_snapshot({
        "raw_value": 0.5,
        "decision_state": "SAFE_ACCESSIBLE",
        "entropy": 0.2,
        "is_blackhole": False
    })
    append_memory_snapshot({
        "raw_value": 0.0,
        "decision_state": "BLACKHOLE",
        "entropy": 1.0,
        "is_blackhole": True
    })

    result = classify_trend(window=5)
    assert result in ("stable", "explore", "collapse", "unknown")

