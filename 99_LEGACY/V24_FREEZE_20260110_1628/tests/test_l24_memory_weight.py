"""
Test V24 — Weighted Memory Layer
"""

import os
import json

from V24_NEXT.l24_memory_weight import append_weighted_memory, V24_MEMORY_FILE

def test_weight_basic():
    entry = append_weighted_memory({
        "raw_value": 0.8,
        "entropy": 0.3,
        "decision_state": "SAFE"
    })

    assert "weight" in entry
    assert entry["weight"] > 0.0

    assert os.path.exists(V24_MEMORY_FILE)
    with open(V24_MEMORY_FILE, "r") as f:
        data = json.load(f)
        assert isinstance(data, list)
        assert len(data) >= 1

