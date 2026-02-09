"""
Test V17 — Export + History
===========================
"""

import os
import json
from V14_NEXT.l14_export_act import run_export_l14_v17

def test_export_and_history():
    ok = run_export_l14_v17(0.7)
    assert ok

