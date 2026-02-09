"""
loventre_meta_energy_curve.py

Per un seed (param, factor) fissato, mostra come cambiano:

  - p_tunnel(E)
  - E[N](E)
  - difficulty_index
  - etichetta di difficoltà

al variare dell'energia E in una griglia di valori.
"""

from typing import List, Tuple

from loventre_meta_engine import meta_analyze_seed


def main() -> None:
    import sys

    # Seed da riga di comando, default = (2,3) critico canonico
    param = 2
    factor = 3

    if len(sys.argv) >= 3:
        try:
            param = int(sys.argv[1])
            factor = int(sys.argv[2])
        except ValueError:
            print("[ATTENZIONE] param/factor non numerici, uso (2,3).")

    # Lista di energie da esplorare (puoi modificarla)
    E_LIST: List[float] = [0.1, 0.2, 0.5, 1.0, 1.5, 2.0]

    print("===============================================================")
    print("=== Loventre Meta–Energy Curve – Seed specifico             ===")
    print("===============================================================")
    print(f"Seed: (param={param}, factor={factor})")
    print(f"Energie testate: {E_LIST}")
    print()

    header = (
        "E       p_tunnel(E)   E[N]          diff_idx  label"
    )
    print(header)
    print("-" * len(header))

    for E in E_LIST:
        f = meta_analyze_seed(param, factor, E)
        full_label = f["difficulty_label"]
        short_label = full_label.split("(")[0].strip()

        print(
            f"{E:5.2f}  "
            f"{f['p_tunnel']:11.3e}  "
            f"{f['expected_attempts']:10.3e}  "
            f"{f['difficulty_index']:8.3f}  "
            f"{short_label}"
        )


if __name__ == "__main__":
    main()
