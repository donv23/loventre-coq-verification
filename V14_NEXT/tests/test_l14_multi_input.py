"""
Test V16 — Multi Input Aggregation
==================================

Verifica:
- corretta ignoranza dei None
- calcolo media/spread
"""

from V14_NEXT.l14_multi_input import compute_multi_input_stats

def test_multi_basic():
    raw = [0.2, 0.5, 0.9]
    stats = compute_multi_input_stats(raw)
    assert stats["n_effective"] == 3
    assert stats["kappa_mean"] > 0.5
    assert stats["kappa_spread"] > 0

def test_multi_with_none():
    raw = [0.9, None, 0.1]
    stats = compute_multi_input_stats(raw)
    assert stats["n_effective"] == 2  # None ignorato

