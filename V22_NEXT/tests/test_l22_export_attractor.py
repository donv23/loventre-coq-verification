"""
Test V22 — Export Attractor Summary
"""

import os
import json

from V21_NEXT.l21_memory_core import append_memory_snapshot
from V22_NEXT.l22_export_attractor import export_attractor_summary, ATTRACTOR_FILE

def test_export_attractor_basic():
    # aggiungiamo un minimo di storia
    append_memory_snapshot({
        "raw_value": 0.4,
        "decision_state": "SAFE",
        "entropy": 0.2,
        "is_blackhole": False
    })

    path = export_attractor_summary(window=10)
    assert os.path.exists(path)

    with open(path, "r") as f:
        data = json.load(f)
        assert "attractor" in data
        assert "transition_counts" in data

