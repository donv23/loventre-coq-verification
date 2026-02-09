"""
Test V18 — Export dinamico
==========================
"""

import os
from V14_NEXT.l14_export_act_dynamic import run_export_l14_dynamic, OUTPUT_DIR

def test_export_dynamic():
    ok = run_export_l14_dynamic(0.8)
    assert ok

