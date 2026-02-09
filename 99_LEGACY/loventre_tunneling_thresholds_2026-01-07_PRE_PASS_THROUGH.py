"""
loventre_tunneling_thresholds.py

Per ogni seed nella griglia toy {1,2,3} x {1,2,3}:

  - calcola un potenziale di barriera V0 (toy) come in loventre_seed_report
    (usando kappa_eff = PATTERN_SCORE, entropy_eff = normalize_spread(spread_long)),
  - per una lista di probabilità target P_TARGETS calcola
        E_star(V0, a_min, p_target)
    cioè l'energia minima (approssimata) necessaria per avere p_tunnel >= p_target.

La formula analitica invertita è (per p_target in (0,1)):

    p_tunnel(V0, a_min, E) = exp( -2 * sqrt(V0 - E) * a_min )

    => sqrt(V0 - E) = - (1 / (2 a_min)) * log(p_target)
    => V0 - E = (log(p_target)^2) / (4 * a_min^2)
    => E = V0 - (log(p_target)^2) / (4 * a_min^2)

Poi clampiamo:
  - E >= 0,
  - E <= V0 (sopra V0 p_tunnel = 1).

Questo ci dà una "energia critica" per portare il problema a una
certa probabilità di lampo di invenzione per tentativo.
"""

import math
from typing import Any, Dict, List

import loventre_seed_report as lsr
from loventre_tunneling import compute_potential
from critical_signature_lab import GRID_SIGNATURES
from loventre_toy_table import get_region, is_P_like, is_NP_like

# Probabilità target per il tunneling
P_TARGETS: List[float] = [1e-3, 1e-2, 1e-1]  # 0.1%, 1%, 10%


def energy_for_target_p(V0: float, a_min: float, p_target: float) -> float:
    """
    Energia minima E_star tale che p_tunnel(V0, a_min, E_star) >= p_target,
    usando la formula invertita per p_tunnel:

        p_tunnel = exp( -2 * sqrt(V0 - E) * a_min )

    con clamp:
      - se p_target >= 1 -> E_star = 0
      - se p_target <= 0 -> E_star = +inf
      - E_star in [0, V0]
    """
    if p_target >= 1.0:
        return 0.0
    if p_target <= 0.0:
        return math.inf

    ln_p = math.log(p_target)  # < 0 per p_target in (0,1)
    delta = (ln_p * ln_p) / (4.0 * (a_min * a_min))
    E_star = V0 - delta

    if E_star < 0.0:
        E_star = 0.0
    if E_star > V0:
        E_star = V0

    return E_star


def main() -> None:
    print("====================================================================")
    print("=== Loventre Tunneling Thresholds – Energia critica per ogni seed ===")
    print("====================================================================")
    print(
        f"Parametri tunneling toy: "
        f"ALPHA={lsr.ALPHA_POTENTIAL}, "
        f"BETA={lsr.BETA_POTENTIAL}, "
        f"A_MIN={lsr.A_MIN_BARRIER}"
    )
    print(f"Probabilità target p_tunnel: {P_TARGETS}")
    print()

    header = (
        "param factor region      P_like NP_like pattern_c                     "
        "V0       " +
        "  ".join([f"E@p={p:0.0e}".ljust(12) for p in P_TARGETS])
    )
    print(header)
    print("-" * len(header))

    for entry in GRID_SIGNATURES:
        param = entry["param"]
        factor = entry["factor"]

        region = get_region(param, factor)
        p_like = is_P_like(param, factor)
        np_like = is_NP_like(param, factor)
        pattern_c = entry["pattern_c"]
        spread_long = float(entry["channels_spread_long"])

        # Stessa compressione toy: kappa_eff = PATTERN_SCORE(pattern_c),
        # entropy_eff = normalize_spread(spread_long)
        pattern_score = lsr.PATTERN_SCORE.get(pattern_c, 0.0)
        spread_norm = lsr.normalize_spread(spread_long)

        kappa_eff = pattern_score
        entropy_eff = spread_norm

        V0 = compute_potential(
            kappa_eff,
            entropy_eff,
            alpha=lsr.ALPHA_POTENTIAL,
            beta=lsr.BETA_POTENTIAL,
        )

        energies: Dict[float, float] = {}
        for p_target in P_TARGETS:
            E_star = energy_for_target_p(V0, lsr.A_MIN_BARRIER, p_target)
            energies[p_target] = E_star

        # Stampa tabellare
        line = (
            f"{param:5d} {factor:6d} "
            f"{region:9} "
            f"{str(p_like):6} {str(np_like):7} "
            f"{pattern_c:30} "
            f"{V0:7.4f}  "
        )

        for p_target in P_TARGETS:
            E_star = energies[p_target]
            if math.isinf(E_star):
                line += f"{'inf':>11} "
            else:
                line += f"{E_star:11.3f} "

        print(line)


if __name__ == "__main__":
    main()
