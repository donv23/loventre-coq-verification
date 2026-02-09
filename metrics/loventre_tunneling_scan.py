"""
loventre_tunneling_scan.py

Scansione dell'intera griglia toy {1,2,3} x {1,2,3}.

Per ogni seed (param, factor) stampa:
  - region (regular / precritical / mixed / critical)
  - P_like / NP_like
  - Pattern C
  - Loventre Score (toy)
  - V0 (potenziale di barriera toy)
  - p_tunnel (probabilità di tunneling per tentativo)
  - E[N] tentativi medi attesi

Usa la stessa configurazione di tunneling definita in loventre_seed_report.py
(ALPHA_POTENTIAL, BETA_POTENTIAL, A_MIN_BARRIER, ENERGY_LEVEL).
"""

from typing import Any, Dict

import loventre_seed_report as lsr
from critical_signature_lab import GRID_SIGNATURES
from loventre_toy_table import (
    get_region,
    is_P_like,
    is_NP_like,
    get_time_short,
    get_time_long,
)


def main() -> None:
    print("===============================================================")
    print("=== Loventre Tunneling Scan – Griglia toy {1,2,3} x {1,2,3} ===")
    print("===============================================================")
    print(
        f"Parametri tunneling toy: "
        f"ALPHA={lsr.ALPHA_POTENTIAL}, "
        f"BETA={lsr.BETA_POTENTIAL}, "
        f"A_MIN={lsr.A_MIN_BARRIER}, "
        f"E={lsr.ENERGY_LEVEL}"
    )
    print()

    header = (
        "param factor region      P_like NP_like pattern_c                     "
        "score    V0       p_tunnel       E[N]"
    )
    print(header)
    print("-" * len(header))

    # GRID_SIGNATURES contiene una entry per ogni (param, factor)
    for entry in GRID_SIGNATURES:
        param = entry["param"]
        factor = entry["factor"]

        region = get_region(param, factor)
        p_like = is_P_like(param, factor)
        np_like = is_NP_like(param, factor)
        pattern_c = entry["pattern_c"]

        score = lsr.compute_loventre_score_from_entry(entry)
        tunneling_info: Dict[str, Any] = lsr.compute_tunneling_from_entry(entry)

        V0 = tunneling_info["V0"]
        p = tunneling_info["p_tunnel"]
        N_mean = tunneling_info["expected_attempts"]

        print(
            f"{param:5d} {factor:6d} "
            f"{region:9} "
            f"{str(p_like):6} {str(np_like):7} "
            f"{pattern_c:30} "
            f"{score:6.3f} "
            f"{V0:7.4f} "
            f"{p:11.3e} "
            f"{N_mean:10.3e}"
        )


if __name__ == "__main__":
    main()
