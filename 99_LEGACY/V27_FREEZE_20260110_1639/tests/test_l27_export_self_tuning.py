"""
V27_NEXT/tests/test_l27_export_self_tuning.py
Test di integrazione per export self-tuning V27.
"""

from pathlib import Path
from V27_NEXT.l27_export_self_tuning import run_export_self_tuning


def test_export_file_created():
    out = run_export_self_tuning(0.45)

    assert isinstance(out, dict)
    assert "self_tuning_outcome" in out

    val = out["self_tuning_outcome"].lower()
    fname = Path(f"V27_JSON_DEMO/v27_self_tuning_{val}.json")

    assert fname.exists(), f"Atteso file {fname}"
    assert fname.stat().st_size > 0

    print("✔ V27 EXPORT SELF TUNING OK")

