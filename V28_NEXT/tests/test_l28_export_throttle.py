"""
V28_NEXT/tests/test_l28_export_throttle.py
Verifica export throttle V28.
"""

from pathlib import Path
from V28_NEXT.l28_export_throttle import run_export_throttle_v28


def test_export_throttle():
    snap = run_export_throttle_v28(0.5)

    assert isinstance(snap, dict)
    assert "adaptive_throttle_decision" in snap

    dec = snap["adaptive_throttle_decision"]
    fname = Path(f"V28_JSON_DEMO/v28_throttle_{dec.lower()}.json")

    assert fname.exists(), f"Atteso file {fname}"
    assert fname.stat().st_size > 0

    print("✔ V28 EXPORT THROTTLE OK")

