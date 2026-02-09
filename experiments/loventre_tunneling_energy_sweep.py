"""
loventre_tunneling_energy_sweep.py

Per ogni seed nella griglia toy {1,2,3} x {1,2,3}, calcola:

  - kappa_eff, entropy_eff, V0 (potenziale di barriera toy)
  - per una lista di energie E_LIST:
      p_tunnel(E) e tentativi medi attesi E[N]

Usa la stessa parametrizzazione toy di loventre_seed_report:
  - ALPHA_POTENTIAL, BETA_POTENTIAL
  - A_MIN_BARRIER
"""

from typing import Any, Dict, List

import loventre_seed_report as lsr
from loventre_tunneling import compute_potential, p_tunnel, expected_attempts
from critical_signature_lab import GRID_SIGNATURES
from loventre_toy_table import get_region, is_P_like, is_NP_like


# Lista di energie da testare (puoi modificarla a piacere)
E_LIST: List[float] = [0.2, 0.5, 1.0, 2.0]


def main() -> None:
    print("======================================================================")
    print("=== Loventre Tunneling Energy Sweep – Griglia toy {1,2,3} x {1,2,3} ===")
    print("======================================================================")
    print(
        f"Parametri tunneling toy: "
        f"ALPHA={lsr.ALPHA_POTENTIAL}, "
        f"BETA={lsr.BETA_POTENTIAL}, "
        f"A_MIN={lsr.A_MIN_BARRIER}"
    )
    print(f"Energie testate: {E_LIST}")
    print()

    for entry in GRID_SIGNATURES:
        param = entry["param"]
        factor = entry["factor"]

        region = get_region(param, factor)
        p_like = is_P_like(param, factor)
        np_like = is_NP_like(param, factor)
        pattern_c = entry["pattern_c"]
        spread_long = float(entry["channels_spread_long"])

        # Stessa compressione toy usata in loventre_seed_report.compute_tunneling_from_entry
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

        print("------------------------------------------------------------------")
        print(f"Seed (param={param}, factor={factor})")
        print(f"  region      : {region}")
        print(f"  P_like      : {p_like}")
        print(f"  NP_like     : {np_like}")
        print(f"  pattern_c   : {pattern_c}")
        print(f"  kappa_eff   : {kappa_eff:.3f}")
        print(f"  entropy_eff : {entropy_eff:.3f}")
        print(f"  V0          : {V0:.4f}")
        print()
        print("  Energia     p_tunnel       E[N] tentativi medi")
        for E in E_LIST:
            p = p_tunnel(V0, lsr.A_MIN_BARRIER, E)
            N_mean = expected_attempts(p)
            print(f"  {E:7.3f}  {p:9.3e}    {N_mean:10.3e}")
        print()

if __name__ == "__main__":
    main()
