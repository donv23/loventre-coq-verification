"""
Test V17 — History Core
=======================
"""

import os
from V14_NEXT.l14_history_core import (
    record_event,
    compute_history_summary,
    HISTORY_DIR,
    HISTORY_FILE,
)


def test_record_and_summary():
    snap = {"state": "SAFE", "kappa_l1": 0.9}
    ok = record_event(snap)
    assert ok

    summary = compute_history_summary()
    assert summary["total"] > 0

