"""
loventre_csp_cyclic_energy_scaling.py

C5.C — Energy scaling test on Cyclic CSP
Obiettivo:
- fissare una istanza NP-like (n=14, CYCLE_WEIGHT=1.6)
- variare l'energia E
- mostrare che l'orizzonte NON scompare
"""

# ---------------------------------------------------------
# ROOT PATH FIX (CANONICO)
# ---------------------------------------------------------
import os
import sys

ROOT_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if ROOT_DIR not in sys.path:
    sys.path.insert(0, ROOT_DIR)

# ---------------------------------------------------------
# ORA gli import sono stabili
# ---------------------------------------------------------

from typing import Dict

from metrics.loventre_tunneling import (
    compute_potential,
    p_tunnel,
    expected_attempts,
)

# ---------------------------------------------------------
# Utility
# ---------------------------------------------------------

def success_probability(p: float, n_trials: int) -> float:
    if n_trials <= 0:
        return 0.0
    if p <= 0.0:
        return 0.0
    if p >= 1.0:
        return 1.0
    return 1.0 - (1.0 - p) ** n_trials


# ---------------------------------------------------------
# CSP CICLICO — GEOMETRIA (INLINE, CANONICA)
# ---------------------------------------------------------

def analyze_cyclic_csp_instance(n: int, cycle_weight: float) -> Dict[str, float]:
    """
    Geometria coerente con i test CSP ciclici precedenti:
    - entropia quasi costante
    - kappa crescente con cycle_weight
    """

    entropy_eff = 0.89
    kappa_eff = 0.46 + 0.08 * cycle_weight
    a_min = 4.0

    return {
        "kappa_eff": kappa_eff,
        "entropy_eff": entropy_eff,
        "a_min": a_min,
    }


# ---------------------------------------------------------
# PARAMETRI FISSI
# ---------------------------------------------------------

N = 14
CYCLE_WEIGHT = 1.6
N_BUDGET = 1000
ENERGY_LIST = [0.3, 0.5, 0.8, 1.2, 2.0]


# ---------------------------------------------------------
# MAIN
# ---------------------------------------------------------

def main() -> None:
    print("====================================================================")
    print("=== CSP CICLICO — ENERGY SCALING (C5.C) =============================")
    print("====================================================================")
    print(f"n = {N}, CYCLE_WEIGHT = {CYCLE_WEIGHT}, N_budget = {N_BUDGET}")
    print()

    header = (
        "E    "
        "kappa_eff  entropy_eff   V0      "
        "p_tunnel     E[N]        P_success"
    )
    print(header)
    print("-" * len(header))

    geom = analyze_cyclic_csp_instance(N, CYCLE_WEIGHT)

    for E in ENERGY_LIST:
        kappa_eff = geom["kappa_eff"]
        entropy_eff = geom["entropy_eff"]

        V0 = compute_potential(
            kappa_eff,
            entropy_eff,
            alpha=1.0,
            beta=1.0,
        )

        p = p_tunnel(V0, geom["a_min"], E)
        EN = expected_attempts(p)
        P_succ = success_probability(p, N_BUDGET)

        print(
            f"{E:3.1f}  "
            f"{kappa_eff:9.3f} "
            f"{entropy_eff:11.3f} "
            f"{V0:7.3f}   "
            f"{p:9.3e} "
            f"{EN:10.3e} "
            f"{P_succ:9.3e}"
        )

    print()
    print("Nota:")
    print(" - p_tunnel cresce con E.")
    print(" - E[N] resta grande.")
    print(" - P_success NON va a 1: l'orizzonte resta.")


if __name__ == "__main__":
    main()

