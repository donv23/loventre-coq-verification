"""
V29_NEXT/tests/test_l29_export_resonance.py
Verifica export JSON V29.
"""

from pathlib import Path
from V29_NEXT.l29_export_resonance import run_export_resonance_v29


def test_export_resonance():
    snap = run_export_resonance_v29([0.1, 0.3, 0.15, 0.22])

    assert isinstance(snap, dict)
    assert "risk_resonance_class" in snap

    dec = snap["risk_resonance_class"].lower()
    fname = Path(f"V29_JSON_DEMO/v29_resonance_{dec}.json")

    assert fname.exists(), f"Atteso file {fname}"
    assert fname.stat().st_size > 0

    print("✔ V29 EXPORT RESONANCE OK")

