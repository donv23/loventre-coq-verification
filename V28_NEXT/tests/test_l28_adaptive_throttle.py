"""
V28_NEXT/tests/test_l28_adaptive_throttle.py
Verifica le 3 bande di adaptive throttle.
"""

from V28_NEXT.l28_adaptive_throttle import compute_adaptive_throttle


def test_l28_ranges():
    assert compute_adaptive_throttle(0.0) == "BOOST"
    assert compute_adaptive_throttle(0.2) == "BOOST"
    assert compute_adaptive_throttle(0.5) == "HOLD"
    assert compute_adaptive_throttle(0.9) == "REDUCE"
    print("✔ V28 ADAPTIVE THROTTLE OK")

