#!/usr/bin/env python3
# ============================================================
# LOVENTRE — PRE-CRITICAL OBSERVER (v1.1)
# ============================================================
# - Osservatore puro
# - Nessun effetto decisionale
# - Usa solo DELTA (derivate discrete)
# - API stabilizzata (analyze_precritical)
# - Compatibile con v5.3 (freeze)
# ============================================================

from typing import Dict, Any, Optional


def compute_delta(prev: Dict[str, Any], curr: Dict[str, Any], key: str) -> Optional[float]:
    try:
        return float(curr.get(key)) - float(prev.get(key))
    except Exception:
        return None


def detect_precritical_transition(
    prev_metrics: Dict[str, Any],
    curr_metrics: Dict[str, Any],
    *,
    delta_chi_threshold: float = 0.15,
    delta_infoP_threshold: float = 0.25,
    delta_p_tunnel_threshold: float = -0.2,
) -> Dict[str, Any]:
    """
    Rileva una possibile transizione pre-critica basata SOLO su Δ.

    NON modifica:
    - decision
    - risk_class
    - meta_label
    """

    d_chi = compute_delta(prev_metrics, curr_metrics, "chi_compactness")
    d_infoP = compute_delta(prev_metrics, curr_metrics, "informational_potential")
    d_p_tunnel = compute_delta(prev_metrics, curr_metrics, "p_tunnel")

    flags = []

    if d_chi is not None and d_chi >= delta_chi_threshold:
        flags.append("Δchi↑")

    if d_infoP is not None and d_infoP >= delta_infoP_threshold:
        flags.append("ΔinfoP↑")

    if d_p_tunnel is not None and d_p_tunnel <= delta_p_tunnel_threshold:
        flags.append("Δp_tunnel↓")

    pre_critical = len(flags) >= 2

    return {
        "pre_critical_flag": pre_critical,
        "pre_critical_signals": flags,
        "delta_chi_compactness": d_chi,
        "delta_informational_potential": d_infoP,
        "delta_p_tunnel": d_p_tunnel,
    }


# ============================================================
# API CANONICA — alias stabile
# ============================================================

def analyze_precritical(prev_metrics: Dict[str, Any],
                        curr_metrics: Dict[str, Any]) -> Dict[str, Any]:
    """
    Alias canonico per integrazione con altri observer.
    """
    return detect_precritical_transition(prev_metrics, curr_metrics)


# ============================================================
# DEMO STANDALONE
# ============================================================

if __name__ == "__main__":

    prev = {
        "chi_compactness": 0.25,
        "informational_potential": 0.45,
        "p_tunnel": 0.7,
    }

    curr = {
        "chi_compactness": 0.45,
        "informational_potential": 0.8,
        "p_tunnel": 0.4,
    }

    report = analyze_precritical(prev, curr)

    print("=== PRE-CRITICAL OBSERVER ===")
    for k, v in report.items():
        print(f"{k:32}: {v}")

