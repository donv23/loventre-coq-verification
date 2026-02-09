"""
loventre_short_summary_inspect.py

Scopo:
  - Chiamare pipeline_regimes_lab.run_experiment per alcuni seed
    (es. (1,1) regolare e (2,3) critico),
  - Ispezionare la struttura dell'oggetto summary che ritorna,
    per capire se contiene curvature/entropy short riutilizzabili
    per definire un potenziale U_short più realistico.
"""

from pprint import pprint
from typing import Any

from pipeline_regimes_lab import run_experiment


def inspect_summary_for_seed(param: int, factor: int) -> None:
    print("================================================================")
    print(f"=== Ispezione summary short per seed (param={param}, factor={factor}) ===")
    print("================================================================")

    # run_experiment stampa sempre il report; vediamo anche cosa ritorna come valore.
    summary = run_experiment(param, factor)

    print("\nTipo di summary:", type(summary))

    if summary is None:
        print("[INFO] summary è None (la funzione non ritorna niente).")
        return

    if isinstance(summary, dict):
        print("\nChiavi presenti in summary:")
        for k, v in summary.items():
            v_type = type(v)
            extra = ""
            if isinstance(v, list):
                extra = f" (lista, len={len(v)})"
            elif isinstance(v, dict):
                extra = f" (dict, len={len(v.keys())})"
            print(f"  - {k!r}: {v_type}{extra}")

        print("\nContenuto (pprint limitato):")
        pprint(summary)
    else:
        print("\nsummary NON è un dict, valore:")
        pprint(summary)


def main() -> None:
    # Seed regolare
    inspect_summary_for_seed(1, 1)
    print("\n\n")
    # Seed critico canonico
    inspect_summary_for_seed(2, 3)


if __name__ == "__main__":
    main()
