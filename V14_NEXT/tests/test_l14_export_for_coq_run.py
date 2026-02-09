"""
Test V19 — Export Coq JSON
"""

import os
from V14_NEXT.l14_export_for_coq import run_export_for_coq_v19, EXPORT_DIR

def test_export_for_coq():
    ok = run_export_for_coq_v19(0.77)
    assert ok
    found = False
    for fname in os.listdir(EXPORT_DIR):
        if fname.startswith("lmetrics_coq_u0_77"):
            found = True
    assert found

