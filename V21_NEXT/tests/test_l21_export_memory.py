"""
Test V21 — export memory summary
"""

import os
import json

from V21_NEXT.l21_memory_core import append_memory_snapshot
from V21_NEXT.l21_export_memory import export_summary, SUMMARY_FILE

def test_export_summary_basic():
    # aggiungi almeno un record
    append_memory_snapshot({
        "raw_value": 0.7,
        "decision_state": "SAFE",
        "entropy": 0.2,
        "is_blackhole": False
    })

    path = export_summary(window=10)
    assert os.path.exists(path)

    with open(path, "r") as f:
        data = json.load(f)
        assert "trend" in data
        assert "safe_count" in data

