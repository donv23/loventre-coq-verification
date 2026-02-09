"""
L14_ENTROPY — V15
=================

Introduzione di entropy_eff alla pipeline V14.

Regola piecewise:
- None → None
- <0.3 → 0.8
- <0.7 → 0.5
- >=0.7 → 0.2
"""

def compute_entropy_eff(kappa_l1):
    if kappa_l1 is None:
        return None
    try:
        k = float(kappa_l1)
    except Exception:
        return None

    if k < 0.3:
        return 0.8
    if k < 0.7:
        return 0.5
    return 0.2

