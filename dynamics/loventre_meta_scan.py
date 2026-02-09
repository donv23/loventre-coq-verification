"""
loventre_meta_scan.py

Scansione del meta–algoritmo Loventre su tutta la griglia toy {1,2,3} x {1,2,3}
per un dato livello di energia E.

Per ogni seed stampa:
  - struttura (region, P_like/NP_like, Pattern C)
  - Loventre Score
  - potenziale V0
  - p_tunnel(E), E[N]
  - difficulty_index
  - etichetta di difficoltà
"""

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


def main() -> None:
    import sys

    # Energia da riga di comando, di default usiamo l'ENERGY_LEVEL del seed_report
    energy = lsr.ENERGY_LEVEL
    if len(sys.argv) >= 2:
        try:
            energy = float(sys.argv[1])
        except ValueError:
            print("[ATTENZIONE] Energia non numerica, uso ENERGY_LEVEL di default.")

    print("===================================================================")
    print("=== Loventre Meta–Scan – Griglia toy {1,2,3} x {1,2,3}         ===")
    print("===================================================================")
    print(f"Energia E = {energy}")
    print()

    header = (
        "param factor region      P_like NP_like "
        "pattern_c                     "
        "score    V0       p_tunnel(E)   E[N]        diff_idx  label"
    )
    print(header)
    print("-" * len(header))

    for (param, factor) in SEEDS:
        f = meta_analyze_seed(param, factor, energy)

        # Short label per la difficoltà (prima parte prima della parentesi)
        full_label = f["difficulty_label"]
        short_label = full_label.split("(")[0].strip()

        print(
            f"{param:5d} {factor:6d} "
            f"{f['region']:9} "
            f"{str(f['P_like']):6} {str(f['NP_like']):7} "
            f"{f['pattern_c']:30} "
            f"{f['loventre_score']:6.3f} "
            f"{f['V0']:7.4f} "
            f"{f['p_tunnel']:11.3e} "
            f"{f['expected_attempts']:10.3e} "
            f"{f['difficulty_index']:8.3f} "
            f"{short_label}"
        )


if __name__ == "__main__":
    main()
