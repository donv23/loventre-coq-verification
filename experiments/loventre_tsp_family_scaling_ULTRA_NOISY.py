"""
loventre_tsp_family_scaling_ULTRA_NOISY.py

C5.A — Entropy stress test:
TSP con coordinate quasi uniformemente random.
Obiettivo: entropia alta, ma geometria NON chiusa.

Se il modello Loventre è corretto:
- H_eff ~ 1
- kappa_eff ~ costante
- V0 limitato
- P_success alto (P-like)
"""

import random
from typing import List, Tuple, Dict

# ---- import TSP toy (canonico) ----
from loventre_tsp_toy import (
    explore_tsp_instance,
    aggregate_tsp_geometry,
)

# ---- import tunneling (CANONICO: metrics/) ----
from metrics.loventre_tunneling import (
    compute_potential,
    p_tunnel,
    expected_attempts,
)

# ---- parametri Loventre ----
ALPHA_TSP = 1.0
BETA_TSP = 1.0
A_MIN_TSP = 4.0


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
# TSP ULTRA-NOISY
# ---------------------------------------------------------

def generate_ultra_noisy_coords(
    n_cities: int,
    seed: int = 42,
) -> List[Tuple[float, float]]:
    """
    Coordinate quasi uniformi in [0,1]^2.
    Entropia alta, nessuna struttura globale.
    """
    rnd = random.Random(seed + 100 * n_cities)
    return [(rnd.random(), rnd.random()) for _ in range(n_cities)]


def max_states_for_n(n: int) -> int:
    if n <= 8:
        return 30000
    if n <= 12:
        return 50000
    return 80000


def analyze_instance(n: int, E: float, N_budget: int) -> Dict[str, float]:
    coords = generate_ultra_noisy_coords(n)
    max_states = max_states_for_n(n)

    metrics_list, _, _ = explore_tsp_instance(coords, max_states=max_states)
    kappa_eff, entropy_eff = aggregate_tsp_geometry(metrics_list)

    V0 = compute_potential(
        kappa_eff,
        entropy_eff,
        alpha=ALPHA_TSP,
        beta=BETA_TSP,
    )

    p = p_tunnel(V0, A_MIN_TSP, E)
    EN = expected_attempts(p)
    P_succ = success_probability(p, N_budget)

    return {
        "n": n,
        "kappa_eff": kappa_eff,
        "entropy_eff": entropy_eff,
        "V0": V0,
        "p_tunnel": p,
        "EN": EN,
        "P_success": P_succ,
    }


# ---------------------------------------------------------
# MAIN
# ---------------------------------------------------------

def main() -> None:
    E = 0.5
    N_budget = 1000
    n_list = [6, 8, 10, 12, 15, 18, 20]

    print("==============================================================")
    print("=== TSP ULTRA-NOISY — C5.A (Entropy stress test) =============")
    print("==============================================================")
    print(f"E = {E}, N_budget = {N_budget}")
    print()

    print("n  kappa_eff  entropy_eff   V0      p_tunnel   E[N]     P_success")
    print("------------------------------------------------------------------")

    for n in n_list:
        r = analyze_instance(n, E, N_budget)
        print(
            f"{r['n']:2d} "
            f"{r['kappa_eff']:9.3f} "
            f"{r['entropy_eff']:11.3f} "
            f"{r['V0']:7.3f} "
            f"{r['p_tunnel']:9.3e} "
            f"{r['EN']:9.2e} "
            f"{r['P_success']:9.3e}"
        )


if __name__ == "__main__":
    main()

