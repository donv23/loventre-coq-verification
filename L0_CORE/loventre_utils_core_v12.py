"""
L0_CORE / loventre_utils_core_v12.py
Funzioni base di utilità numerica nate per essere usate a cascata.
"""

# -----------------------------------------------------------
# safe_numeric
# -----------------------------------------------------------
def safe_numeric(x):
    """
    Prova a convertire un input in float.
    Restituisce 0.0 se None o conversione impossibile.
    """
    if x is None:
        return 0.0
    try:
        return float(x)
    except Exception:
        return 0.0

# -----------------------------------------------------------
# clamp01
# -----------------------------------------------------------
def clamp01(x):
    """
    Mantiene il valore in [0,1].
    None → 0.5 (valore neutrale).
    """
    if x is None:
        return 0.5
    try:
        f = float(x)
    except:
        return 0.5
    if f < 0.0:
        return 0.0
    if f > 1.0:
        return 1.0
    return f

# -----------------------------------------------------------
# safe_neg
# -----------------------------------------------------------
def safe_neg(x):
    """
    Converte in numero e restituisce l'opposto.
    None → 0.0
    """
    v = safe_numeric(x)
    return -v

# -----------------------------------------------------------
# safe_zero_if_none
# -----------------------------------------------------------
def safe_zero_if_none(x):
    """
    None → 0.0, altrimenti float(x)
    """
    return safe_numeric(x)

# -----------------------------------------------------------
# mini-demo
# -----------------------------------------------------------
if __name__ == "__main__":
    print("=== DEMO UTILS CORE V12 ===")
    print("safe_numeric(None)    →", safe_numeric(None))
    print("safe_numeric('ciao')  →", safe_numeric("ciao"))
    print("safe_numeric(7.2)     →", safe_numeric(7.2))
    print("clamp01(None)         →", clamp01(None))
    print("clamp01(2.3)          →", clamp01(2.3))
    print("clamp01(-4.0)         →", clamp01(-4.0))
    print("safe_neg(3)           →", safe_neg(3))
    print("safe_neg(None)        →", safe_neg(None))
    print("safe_zero_if_none(None) →", safe_zero_if_none(None))

