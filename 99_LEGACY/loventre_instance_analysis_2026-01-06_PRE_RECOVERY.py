"""
loventre_instance_analysis.py
--------------------------------
Versione blindata compatibile Python 3.8+
Compatibile con validate_metrics_bus() e tutte le demo.
"""

import math
import random
from typing import Any, Dict, List, Optional
from loventre_metrics_bus import ensure_loventre_keys


# ============================================================
# Bus base completo
# ============================================================

def _default_loventre_bus() -> Dict[str, Any]:
    """Crea un bus Loventre completo conforme al contratto del Metrics Bus."""
    return {
        "region": "R00",
        "kappa_eff": 0.0,
        "entropy_eff": 0.0,
        "V0": 0.0,
        "a_min": 1.0,
        "p_tunnel": 1e-3,
        "P_success": 1.0,
        "gamma_dilation": 1.0,
        "time_regime": "time_euclidean",
        "mass_eff": 1.0,
        "inertial_idx": 1.0,
        "risk_index": 0.0,
        "risk_class": "risk_LOW",
        "chi_compactness": 0.0,
        "horizon_flag": False,
        "meta_label": "meta_unknown",
        "loventre_global_decision": "GD_invalid",
        "loventre_global_color": "GC_green",
        "loventre_global_score": 0.0,
    }


# ============================================================
# Analisi istanza (compatibile stringa o history)
# ============================================================

def analyze_instance(source: Any, energy: float = 0.5, **kwargs) -> Dict[str, Any]:
    bus = _default_loventre_bus()

    if isinstance(source, str):
        random.seed(hash(source) % (2**32))
        bus["kappa_eff"] = round(random.uniform(0.0, 2.0), 3)
        bus["entropy_eff"] = round(random.uniform(0.0, 1.0), 3)
    elif isinstance(source, list) and source and isinstance(source[0], dict):
        C_vals = [float(s.get("C", 0.0)) for s in source]
        H_vals = [float(s.get("H", 0.0)) for s in source]
        bus["kappa_eff"] = round(sum(C_vals) / len(C_vals), 3)
        bus["entropy_eff"] = round(sum(H_vals) / len(H_vals), 3)
    else:
        raise ValueError("Parametro 'source' non valido per analyze_instance.")

    bus["V0"] = round(0.5 * bus["kappa_eff"], 3)
    bus["a_min"] = 1.0 + 0.1 * bus["entropy_eff"]
    bus["p_tunnel"] = round(math.exp(-bus["V0"] / max(energy, 1e-6)), 6)
    bus["P_success"] = round(1.0 - bus["p_tunnel"], 6)
    bus["gamma_dilation"] = round(1.0 + 0.1 * bus["entropy_eff"], 3)
    bus["risk_index"] = round(10.0 * bus["p_tunnel"], 3)
    bus["chi_compactness"] = round(0.1 * bus["kappa_eff"], 3)
    bus["horizon_flag"] = bus["risk_index"] >= 8.0

    if bus["risk_index"] < 3.0:
        bus["risk_class"] = "risk_LOW"
        bus["meta_label"] = "meta_P_like_like"
        bus["loventre_global_decision"] = "GD_safe"
        bus["loventre_global_color"] = "GC_green"
    elif bus["risk_index"] < 7.0:
        bus["risk_class"] = "risk_MID"
        bus["meta_label"] = "meta_P_like_accessible"
        bus["loventre_global_decision"] = "GD_borderline"
        bus["loventre_global_color"] = "GC_yellow"
    else:
        bus["risk_class"] = "risk_NP_like_black_hole"
        bus["meta_label"] = "meta_NP_like_black_hole"
        bus["loventre_global_decision"] = "GD_retreat"
        bus["loventre_global_color"] = "GC_red"

    bus["loventre_global_score"] = round(1.0 - 0.1 * bus["risk_index"], 3)
    bus["time_regime"] = "time_hyperbolic" if bus["gamma_dilation"] > 5.0 else "time_euclidean"

    return ensure_loventre_keys(bus)


# ============================================================
# Enrichment: tempo e massa
# ============================================================

def enrich_metrics_with_time_dilation(metrics: Dict[str, Any], **kwargs) -> Dict[str, Any]:
    if "kappa_eff" not in metrics:
        metrics["kappa_eff"] = 0.0
    if "entropy_eff" not in metrics:
        metrics["entropy_eff"] = 0.0
    if "gamma_dilation" not in metrics:
        metrics["gamma_dilation"] = 1.0

    gamma = float(metrics.get("gamma_dilation", 1.0))
    entropy = float(metrics.get("entropy_eff", 0.0))
    risk = float(metrics.get("risk_index", 0.0))
    cap = kwargs.get("gamma_cap", 100.0)

    new_gamma = round(min(gamma * (1.0 + 0.05 * entropy), cap), 3)
    regime = "time_euclidean" if risk < 5.0 else "time_hyperbolic"

    metrics.update({
        "gamma_dilation": new_gamma,
        "time_regime": regime,
    })
    return ensure_loventre_keys(metrics)


def enrich_metrics_with_mass(metrics: Dict[str, Any], history: Optional[List[Dict[str, float]]] = None,
                             m0: float = 1.0, w_C: float = 1.0, w_H: float = 0.5, **kwargs) -> Dict[str, Any]:
    """Compatibile con firma usata in loventre_global_profile_lab.py"""
    if history:
        mean_C = sum(float(s.get("C", 0.0)) for s in history) / len(history)
        mean_H = sum(float(s.get("H", 0.0)) for s in history) / len(history)
    else:
        mean_C, mean_H = 0.0, 0.0

    mass = m0 + w_C * mean_C + w_H * mean_H
    gamma = float(metrics.get("gamma_dilation", 1.0))
    metrics.update({
        "mass_eff": round(mass, 3),
        "inertial_idx": round(mass * gamma, 3),
    })
    return ensure_loventre_keys(metrics)


# ============================================================
# Strategia euristica
# ============================================================

def suggest_strategy(metrics: Dict[str, Any]) -> str:
    risk = metrics.get("risk_index", 0.0)
    label = metrics.get("meta_label", "")
    if risk < 3.0:
        return f"[SAFE] Prosegui – {label}"
    elif risk < 7.0:
        return f"[ACCESSIBLE] Valuta – {label}"
    return f"[CRITICAL] Ritira – {label}"


# ============================================================
# Self test
# ============================================================

if __name__ == "__main__":
    demo = analyze_instance("demo_seed_1_1")
    demo = enrich_metrics_with_mass(enrich_metrics_with_time_dilation(demo))
    print("=== LOVENTRE INSTANCE ANALYSIS (self-test) ===")
    for k, v in demo.items():
        print(f"{k:26}: {v}")
    print("Strategy:", suggest_strategy(demo))

