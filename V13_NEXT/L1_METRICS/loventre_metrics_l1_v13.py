"""
L1_METRICS — V13
================

Misura e normalizza un input grezzo in kappa_l1 ∈ [0,1].

Output L1 è un dizionario con forma:
    {
        "kappa_l1": <float or None>
    }

Regole:
- safe_numeric converte input in numero o None
- clamp01 limita il valore a [0.0, 1.0]
- output sempre dict, mai raw float
"""

from V13_NEXT.L0_CORE_v13_utils import safe_numeric, clamp01

def compute_l1_metrics_v13(raw_input):
    """
    Trasforma un input grezzo in un dizionario L1.
    """
    v = safe_numeric(raw_input)
    kappa = clamp01(v)
    return {
        "kappa_l1": kappa
    }

