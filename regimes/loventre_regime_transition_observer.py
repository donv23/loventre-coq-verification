#!/usr/bin/env python3
"""
Loventre Regime Transition Observer
----------------------------------
Osservatore descrittivo per transizioni di regime.
Integra (passivamente) il Pre-Critical Observer.
Nessun impatto decisionale.
"""

import json
import sys
from typing import Dict, Any, Optional

from loventre_precritical_observer import analyze_precritical


def print_step_header(step: int) -> None:
    print()
    print(f"--- STEP {step} ---")


def print_metric(metrics: Dict[str, Any], key: str) -> None:
    print(f"{key:<28}: {metrics.get(key)}")


def compute_delta(curr: Dict[str, Any],
                  prev: Dict[str, Any],
                  key: str) -> Optional[float]:
    try:
        return float(curr[key]) - float(prev[key])
    except Exception:
        return None


def main() -> None:
    if len(sys.argv) != 2:
        print("Usage: loventre_regime_transition_observer.py <sequence.json>")
        sys.exit(1)

    path = sys.argv[1]
    with open(path, "r", encoding="utf-8") as f:
        sequence = json.load(f)

    if not isinstance(sequence, list):
        raise ValueError("Il file JSON deve contenere una lista di step.")

    prev_metrics: Optional[Dict[str, Any]] = None

    print("\n=== REGIME TRANSITION OBSERVER ===")

    for i, metrics in enumerate(sequence):
        print_step_header(i)

        # --- Stato principale ---
        for k in [
            "C_regime",
            "risk_index",
            "chi_compactness",
            "p_tunnel",
            "informational_potential",
            "informational_inertia",
            "horizon_flag",
            "meta_label",
        ]:
            print_metric(metrics, k)

        # --- Delta ---
        if prev_metrics is not None:
            print("\nΔ (delta rispetto allo step precedente):")
            for k in [
                "risk_index",
                "chi_compactness",
                "p_tunnel",
                "informational_potential",
                "informational_inertia",
            ]:
                d = compute_delta(metrics, prev_metrics, k)
                if d is not None:
                    print(f"Δ{k:<27}: {d}")

            # --- Pre-critical observer (PASSIVO) ---
            pre = analyze_precritical(prev_metrics, metrics)

            if pre.get("pre_critical_flag"):
                print("\n[Pre-Critical Observer]")
                print(f"pre_critical_flag      : True")
                print(f"pre_critical_signals   : {pre.get('pre_critical_signals')}")
            else:
                print("\n[Pre-Critical Observer]")
                print("pre_critical_flag      : False")

        prev_metrics = metrics


if __name__ == "__main__":
    main()

