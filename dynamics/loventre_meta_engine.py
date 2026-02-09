"""
loventre_meta_engine.py
Legacy + Canonical Metrics Collector
Ripristino controllato — FASE 4.1
"""

# =========================================================
# IMPORT CANONICI
# =========================================================

from typing import Dict

from loventre_robustness_stack_v1 import append_robustness_stack_v1


# =========================================================
# RACCOLTA METRICHE CANONICA (FASE 4.1)
# =========================================================

def loventre_collect_base_metrics(seed: dict) -> dict:
    """
    Raccolta canonica delle metriche Loventre (FASE 4.1)
    """
    param = seed.get("param", 0)
    factor = seed.get("factor", 0)

    # metriche di base (placeholder deterministico)
    kappa_eff = float(param)
    entropy_eff = float(factor)
    V0 = kappa_eff * entropy_eff

    # nuove metriche FASE 4
    p_tunnel = 1.0 / (1.0 + V0)
    P_success = p_tunnel * (1.0 + kappa_eff)

    return {
        "kappa_eff": kappa_eff,
        "entropy_eff": entropy_eff,
        "V0": V0,
        "p_tunnel": p_tunnel,
        "P_success": P_success,

        # legacy (immutato)
        "time_regime": "legacy",
        "risk_class": "legacy",
        "barrier_kappa": kappa_eff,
        "barrier_entropy": entropy_eff,
        "barrier_V0": V0,
    }


# =========================================================
# ENTRY POINT CANONICO (NUOVO)
# =========================================================

def loventre_collect_metrics_with_robustness(seed: Dict[str, int]) -> Dict[str, object]:
    """
    Entry point canonico:
    - raccoglie metriche base
    - applica Robustness Stack v1
    - restituisce metrics bus arricchito
    """

    base_metrics = loventre_collect_base_metrics(seed)

    enriched_metrics = append_robustness_stack_v1(
        base_metrics,
        seed,
        engine_fn=loventre_collect_base_metrics,
    )

    return enriched_metrics


# =========================================================
# DIAGNOSTICA LEGACY (INTATTA)
# =========================================================

def compute_barrier_diagnostic_v4(metrics: dict) -> str:
    """
    Diagnostica legacy SAFE / WARNING / BLACKHOLE
    (NON MODIFICATA)
    """
    kappa = metrics.get("kappa_eff", 0.0)
    entropy = metrics.get("entropy_eff", 0.0)

    if kappa < 1.0 and entropy < 1.0:
        return "SAFE"
    elif kappa >= 1.0 and entropy < 1.0:
        return "WARNING"
    else:
        return "BLACKHOLE"


# =========================================================
# ENTRY POINT LEGACY (PRESERVATO)
# =========================================================

def main(seed: dict) -> str:
    metrics = loventre_collect_base_metrics(seed)
    return compute_barrier_diagnostic_v4(metrics)

