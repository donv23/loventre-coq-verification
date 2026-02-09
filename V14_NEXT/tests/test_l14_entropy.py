"""
Test V14 — Entropy Eff
======================

Verifica:
- None handling
- Fasce piecewise corrette
"""

from V14_NEXT.l14_entropy import compute_entropy_eff

def test_entropy_none():
    assert compute_entropy_eff(None) is None

def test_entropy_low():
    assert compute_entropy_eff(0.1) == 0.8

def test_entropy_mid():
    assert compute_entropy_eff(0.5) == 0.5

def test_entropy_high():
    assert compute_entropy_eff(0.9) == 0.2

