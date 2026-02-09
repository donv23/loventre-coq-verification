"""
Test V14 — Export Act
=====================

Verifica che:
- il writer crea 3 file
- tutti sono schema-valid
"""

import os
from V14_NEXT.l14_export_act import run_export_l14_v13_cases, OUTPUT_DIR
from V14_NEXT.l14_schema_validator import validate_schema_v14
import json

def test_l14_export_act():
    ok = run_export_l14_v13_cases()
    assert ok, "Export act deve ritornare True"

    # verifica presenza file
    fnames = [
        "v14_case_safe.json",
        "v14_case_safe_accessible.json",
        "v14_case_blackhole.json"
    ]
    for fn in fnames:
        path = os.path.join(OUTPUT_DIR, fn)
        assert os.path.exists(path), f"Manca file exportato: {fn}"

        with open(path, "r") as f:
            data = json.load(f)

        assert validate_schema_v14(data), f"File {fn} non rispetta schema"

