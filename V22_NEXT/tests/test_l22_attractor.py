"""
Test V22 — Attractor Classifier
"""
from V21_NEXT.l21_memory_core import append_memory_snapshot
from V22_NEXT.l22_attractor import classify_attractor

def test_attractor_classifier_basic():
    # crea un po' di storia sicura
    append_memory_snapshot({
        "raw_value": 0.6,
        "decision_state": "SAFE",
        "entropy": 0.1,
        "is_blackhole": False
    })
    append_memory_snapshot({
        "raw_value": 0.8,
        "decision_state": "SAFE",
        "entropy": 0.2,
        "is_blackhole": False
    })

    result = classify_attractor(window=5)
    assert result in ("stable_basin", "expansion", "blackhole_sink", "undefined")

