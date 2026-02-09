"""
V29_NEXT/tests/test_l29_risk_resonance.py
Test varianza per classi rischio.
"""

from V29_NEXT.l29_risk_resonance import compute_risk_resonance


def test_l29_resonance_bins():
    assert compute_risk_resonance([0.10, 0.11, 0.09]) == "CALM"
    assert compute_risk_resonance([0.1, 0.3, 0.15, 0.22]) == "PULSED"
    assert compute_risk_resonance([0.0, 1.0, 0.0, 1.0]) == "RESONANT"
    print("✔ V29 RISK RESONANCE OK")

