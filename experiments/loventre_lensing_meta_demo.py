from __future__ import annotations

import random
from typing import Any, Dict, List

from loventre_lensing_geodesic_lab import geodesic_lensed_walk
from loventre_meta_decision_engine import meta_decide_instance_with_mass
from loventre_theory_bridge_seed import print_einstein_loventre_quick_summary


State = Dict[str, Any]


def build_lensing_history(
    steps: int = 40,
    num_neighbors: int = 12,
) -> List[Dict[str, float]]:
    """
    Genera una history [ {C,H}, ... ] usando la geodesic_lensed_walk,
    riusando esattamente lo schema di lenti del lab.
    """

    random.seed(123)

    # Lenti come nel main del lab:
    lenses = [
        {"pos": (0.0, 0.0), "mass": 3.0, "kind": "attractor"},
        {"pos": (2.0, 2.0), "mass": 2.0, "kind": "repulsor"},
    ]

    start_state: State = {
        "C": 0.5,
        "H": 0.5,
        "pos": (0.0, 0.0),
    }

    path = geodesic_lensed_walk(
        start_state=start_state,
        steps=steps,
        num_neighbors=num_neighbors,
        lenses=lenses,
        alpha=1.0,
        beta=1.0,
        G_L=1.0,
        lambda_L=0.0,
        a_geod=1.0,
        b_geod=1.0,
        c_geod=0.0,
        m0=1.0,
        w_C=1.0,
        w_H=0.5,
        inertia_weight=1.0,
        lens_weight=1.0,
    )

    # History per la meta-decisione: solo (C,H)
    history: List[Dict[str, float]] = []
    for row in path:
        C_val = float(row.get("C", 0.0))
        H_val = float(row.get("H", 0.0))
        history.append({"C": C_val, "H": H_val})

    return history


def main() -> None:
    history = build_lensing_history(steps=40, num_neighbors=12)

    result = meta_decide_instance_with_mass(
        history,
        E=1.5,
        alpha=1.0,
        beta=1.0,
        G_L=1.0,
        lambda_L=0.0,
        V0=None,
        V0_quantile=0.9,
        p_target=0.1,
        gamma_cap=100.0,
    )

    print()
    print("==============================================================")
    print("=== LOVENTRE LENSING + META-DECISION DEMO                   ===")
    print("==============================================================")
    print(f"Lunghezza history (steps+1): {len(history)}")
    print()

    print("--- QUICK EINSTEIN–LOVENTRE SUMMARY (lensing) ---")
    print_einstein_loventre_quick_summary(result)

    print()
    print("--- META-EXPLANATION COMPLETA (con Hawking / Planck / Policy) ---")
    print(result.get("meta_explanation", ""))


if __name__ == "__main__":
    main()

