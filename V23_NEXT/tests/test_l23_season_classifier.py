"""
Test V23 — Season Classifier
"""

from V21_NEXT.l21_memory_core import append_memory_snapshot
from V23_NEXT.l23_season_classifier import classify_season

def test_season_classifier_basic():
    append_memory_snapshot({
        "raw_value": 0.9,
        "decision_state": "SAFE_ACCESSIBLE",
        "entropy": 0.3,
        "is_blackhole": False
    })

    season = classify_season(window=10)
    assert season in ("spring", "summer", "autumn", "winter", "unknown")

