"""
loventre_meta_budget_thresholds.py

Dato:
  - un livello di energia E
  - una lista di probabilità target P_target (es. [0.5, 0.9, 0.99])

per ogni seed della griglia toy {1,2,3} x {1,2,3} calcola il numero minimo
di tentativi N_min necessario a raggiungere almeno P_target, usando:

    P_success = 1 - (1 - p_tunnel)^N
    N_min = ceil( ln(1 - P_target) / ln(1 - p_tunnel) )

Se p_tunnel è 0, N_min = inf.
"""

import math
from typing import List, Tuple

from loventre_meta_engine import meta_analyze_seed
import loventre_seed_report as lsr


SEEDS: List[Tuple[int, int]] = [
    (1, 1),
    (1, 2),
    (1, 3),
    (2, 1),
    (2, 2),
    (2, 3),
    (3, 1),
    (3, 2),
    (3, 3),
]

# Probabilità target che vogliamo analizzare
P_TARGETS: List[float] = [0.5, 0.9, 0.99]


def _parse_args():
    import sys

    energy = lsr.ENERGY_LEVEL  # default: energia toy (es. 0.5)
    if len(sys.argv) >= 2:
        try:
            energy = float(sys.argv[1])
        except ValueError:
            print("[ATTENZIONE] energia non numerica, uso ENERGY_LEVEL di default.")
    return energy


def required_trials(p: float, p_target: float) -> float:
    """
    Numero minimo di tentativi N per avere P_success >= p_target,
    partendo da probabilità p per singolo tentativo.

    Se p <= 0 -> N = inf.
    Se p >= 1 -> N = 1.
    """
    if p <= 0.0:
        return math.inf
    if p >= 1.0:
        return 1.0
    if p_target <= 0.0:
        return 0.0
    if p_target >= 1.0:
        p_target = 0.999999

    # N >= ln(1 - P_target) / ln(1 - p)
    num = math.log1p(-p_target)   # ln(1 - P_target), negativo
    den = math.log1p(-p)          # ln(1 - p), negativo

    if den == 0.0:
        return math.inf

    N = num / den
    if N < 0:
        return math.inf

    return math.ceil(N)


def main() -> None:
    energy = _parse_args()

    print("===================================================================")
    print("=== Loventre Meta–Budget Thresholds                            ===")
    print("===================================================================")
    print(f"Energia E   : {energy}")
    print(f"Probabilità target: {P_TARGETS}")
    print()

    header = (
        "param factor region      P_like NP_like "
        "pattern_c                     "
        "V0       p_tunnel(E)   "
    )
    for p_t in P_TARGETS:
        header += f"N@P>={p_t:.2f}    "
    print(header)
    print("-" * len(header))

    for (param, factor) in SEEDS:
        f = meta_analyze_seed(param, factor, energy)
        p = f["p_tunnel"]

        line = (
            f"{param:5d} {factor:6d} "
            f"{f['region']:9} "
            f"{str(f['P_like']):6} {str(f['NP_like']):7} "
            f"{f['pattern_c']:30} "
            f"{f['V0']:7.4f} "
            f"{p:11.3e}   "
        )

        for p_t in P_TARGETS:
            N_req = required_trials(p, p_t)
            if math.isinf(N_req):
                line += f"{'inf':>10}   "
            else:
                line += f"{int(N_req):10d}   "

        print(line)


if __name__ == "__main__":
    main()
