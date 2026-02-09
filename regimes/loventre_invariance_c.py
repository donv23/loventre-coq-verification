"""
loventre_invariance_c.py

Formalizzazione ENGINE-FIRST del principio di invarianza C.

C è definita come invariante debole di regime operativo:
- non è globale
- non è definita sulle storie
- non è auto-certificante
- è stabile solo entro uno stesso regime

Compatibile con:
- perdita informativa (λ)
- cambi di regime (κ)
- non auto-certificazione
"""

from typing import Dict, Any


# =========================
# Regime operativo
# =========================

def compute_regime(metrics: Dict[str, Any]) -> str:
    """
    Determina il regime operativo a partire dal metrics bus.

    Questa funzione DEVE essere coerente con il motore esistente.
    Qui usiamo una classificazione minimale e non invasiva.
    """

    U = metrics.get("potential", None)
    if U is None:
        return "undefined"

    U_star = metrics.get("U_threshold", 1.0)

    if U <= U_star:
        return "accessible"
    else:
        return "opaque"


# =========================
# Invarianza C
# =========================

def compute_C(metrics: Dict[str, Any]) -> str:
    """
    Quantità C: classe di regime.

    NOTA:
    - C NON è il valore numerico del potenziale
    - C è una classe discreta stabile entro il regime
    """

    regime = compute_regime(metrics)
    return regime


def same_regime(metrics_1: Dict[str, Any], metrics_2: Dict[str, Any]) -> bool:
    """
    Due stati sono equivalenti se inducono lo stesso regime operativo.
    """

    return compute_regime(metrics_1) == compute_regime(metrics_2)


def C_invariant(metrics_1: Dict[str, Any], metrics_2: Dict[str, Any]) -> bool:
    """
    Verifica operativa dell'invarianza C.

    Se due metrics bus inducono lo stesso regime,
    allora devono avere lo stesso valore di C.
    """

    if not same_regime(metrics_1, metrics_2):
        # fuori dominio: C NON deve essere invariante
        return False

    return compute_C(metrics_1) == compute_C(metrics_2)

