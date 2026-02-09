#!/usr/bin/env python3
# =====================================================================
# LOVENTRE ENGINE — GCT DIAGNOSIS LAYER
# =====================================================================
# Scopo:
#   - fornire una diagnosi STRUTTURALE di coerenza globale
#   - indipendente da policy, score, strategie o colori
#   - compatibile con metrics bus v5.x
#
# NON:
#   - suggerisce azioni
#   - decide strategie
#   - assegna score
#   - risolve istanze
# =====================================================================

from typing import Dict, Any


# ---------------------------------------------------------------------
# Stati canonici della Global Coherence Trichotomy (GCT)
# ---------------------------------------------------------------------

GCT_NO_BARRIER = "GCT_NO_BARRIER"
GCT_CONDUCTANCE_COLLAPSE = "GCT_CONDUCTANCE_COLLAPSE"
GCT_COUPLING_EXPLOSION = "GCT_COUPLING_EXPLOSION"
GCT_MONODROMY_OBSTRUCTION = "GCT_MONODROMY_OBSTRUCTION"
GCT_INCONCLUSIVE = "GCT_INCONCLUSIVE"


# ---------------------------------------------------------------------
# Diagnosi principale
# ---------------------------------------------------------------------

def diagnose_gct(metrics: Dict[str, Any]) -> str:
    """
    Diagnosi strutturale GCT basata esclusivamente su metriche locali.
    Non usa tempo, non usa strategia, non usa decisioni globali.
    """

    try:
        kappa = metrics.get("kappa_eff")
        entropy = metrics.get("entropy_eff")
        chi = metrics.get("chi_compactness")
        horizon = metrics.get("horizon_flag")
        C_regime = metrics.get("C_regime")
    except Exception:
        return GCT_INCONCLUSIVE

    # -------------------------------------------------
    # 1. Conductance Collapse (isole)
    # -------------------------------------------------
    if kappa is not None and abs(kappa) < 0.1:
        return GCT_CONDUCTANCE_COLLAPSE

    # -------------------------------------------------
    # 2. Coupling Explosion (frammentazione)
    # -------------------------------------------------
    if entropy is not None and entropy > 5.0:
        return GCT_COUPLING_EXPLOSION

    # -------------------------------------------------
    # 3. Monodromy Obstruction (torsione diffusa)
    # -------------------------------------------------
    if horizon is True and chi is not None and chi > 1.0:
        return GCT_MONODROMY_OBSTRUCTION

    # -------------------------------------------------
    # 4. Regime coerente (nessuna barriera rilevata)
    # -------------------------------------------------
    if C_regime is not None and C_regime == "INVARIANT":
        return GCT_NO_BARRIER

    # -------------------------------------------------
    # 5. Caso residuo
    # -------------------------------------------------
    return GCT_INCONCLUSIVE


# ---------------------------------------------------------------------
# Helper descrittivo (opzionale)
# ---------------------------------------------------------------------

def gct_is_hard_obstruction(gct_status: str) -> bool:
    """
    Indica se lo stato GCT rappresenta una barriera strutturale forte.
    """
    return gct_status in {
        GCT_CONDUCTANCE_COLLAPSE,
        GCT_COUPLING_EXPLOSION,
        GCT_MONODROMY_OBSTRUCTION,
    }

