"""
Test V16 — Multi Export
=======================

Verifica che venga creato il JSON multi-case.
"""

import os
import json
from V14_NEXT.l14_export_multi import run_export_multi_v16, OUTPUT_DIR

def test_export_multi():
    ok = run_export_multi_v16()
    assert ok

    fname = "v14_multi_case.json"
    path = os.path.join(OUTPUT_DIR, fname)
    assert os.path.exists(path)

    with open(path) as f:
        data = json.load(f)

    assert data["n_effective"] > 0

