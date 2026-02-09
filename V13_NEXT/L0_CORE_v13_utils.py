"""
L0_CORE_v13_utils
=================

Ricrea le funzioni base che erano in L0_CORE nelle versioni precedenti.
Queste utility sono ora parte integrante del mondo V13.

safe_numeric:
    - se input None → ritorna None
    - se input numerico → cast a float
    - altrimenti → None

clamp01:
    - limita valore ∈ [0.0, 1.0]
    - se None → None

Nota:
Non esiste più un layer L0 indipendente:
queste funzioni sono un servizio minimo all’inizio della pipeline.
"""

def safe_numeric(x):
    """Converte input in float se possibile, altrimenti None."""
    if x is None:
        return None
    try:
        return float(x)
    except Exception:
        return None

def clamp01(x):
    """Clampa un numero a [0,1]. None rimane None."""
    if x is None:
        return None
    try:
        xf = float(x)
    except Exception:
        return None
    if xf < 0.0:
        return 0.0
    if xf > 1.0:
        return 1.0
    return xf

