"""
loventre_meta_decision_engine.py
Seed dicembre 2025 – compatibilità completa demo (family, region, mass_global).
"""

from __future__ import annotations
from typing import Any, Dict
from loventre_metrics_bus import ensure_loventre_keys
from loventre_instance_analysis import analyze_instance, suggest_strategy


# ============================================================
# 1. Shim retrocompatibile: _compute_risk_profile
# ============================================================

def _compute_risk_profile(metrics: dict) -> dict:
    """
    Genera un profilo di rischio sintetico.
    """
    risk_val = float(metrics.get("risk_index", 0.0))
    if risk_val < 2.0:
        level = "LOW"
    elif risk_val < 5.0:
        level = "MEDIUM"
    else:
        level = "HIGH"
    return {"risk_level": level, "risk_value": risk_val}


# ============================================================
# 2. Decisione globale (accetta *args / **kwargs per demo legacy)
# ============================================================

def loventre_attach_global_decision_to_metrics(metrics: Dict[str, Any], *args, **kwargs) -> Dict[str, Any]:
    """
    Integra il blocco globale di decisione nel dict delle metriche.
    Accetta e ignora argomenti extra (es. family) per compatibilità.
    """
    m = ensure_loventre_keys(metrics)

    # Gestione opzionale di argomenti legacy
    if "family" in kwargs:
        m["family"] = kwargs["family"]
    if "region" not in m:
        m["region"] = "default_region"

    risk_info = _compute_risk_profile(m)
    strat = suggest_strategy(m)

    if strat == "INSISTI":
        decision, color = "GD_safe", "GC_green"
    elif strat == "CAMBIA_STRATEGIA":
        decision, color = "GD_borderline", "GC_yellow"
    else:
        decision, color = "GD_withdraw", "GC_red"

    m.update({
        "loventre_global_decision": decision,
        "loventre_global_color": color,
        "loventre_global_score": 1.0,
        "risk_profile": risk_info,
    })
    return m


# ============================================================
# 3. Wrapper locale (test standard)
# ============================================================

def meta_decide_instance_with_mass(history, E=1.0):
    base = analyze_instance(history, E=E)
    decided = loventre_attach_global_decision_to_metrics(base)
    return decided


# ============================================================
# 4. Wrapper globale per demo_mass_global_run.py
# ============================================================

def meta_decide_instance_with_mass_global(history, E=1.0, context=None):
    """
    Variante globale del wrapper massivo (compatibilità demo).
    """
    result = meta_decide_instance_with_mass(history, E=E)
    result["context_info"] = context or {"note": "default_context"}
    return result

