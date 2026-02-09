"""
Test V23 — Export Cycles Summary
"""

import os
import json

from V21_NEXT.l21_memory_core import append_memory_snapshot
from V23_NEXT.l23_export_cycles import export_cycle_summary, CYCLE_FILE

def test_export_cycles_basic():
    # nuova osservazione per evitare file vuoti
    append_memory_snapshot({
        "raw_value": 0.3,
        "decision_state": "SAFE",
        "entropy": 0.1,
        "is_blackhole": False
    })

    path = export_cycle_summary(window=10)
    assert os.path.exists(path)

    with open(path, "r") as f:
        data = json.load(f)
        assert "season" in data
        assert "cycle_state" in data
        assert "attractor" in data

