"""
loventre_iterated_summary_inspect.py

Scopo:
  - Chiamare pipeline_multichannel_long_history.run_iterated_experiment
    per alcuni seed (es. (2,3) critico e (1,1) regolare),
  - Ispezionare la struttura dell'oggetto _summary_long che ritorna,
    per capire se contiene serie temporali (history, curvature, entropy, ecc.)
    riutilizzabili come lista di potenziali U(t).
"""

from pprint import pprint
from typing import Any

from pipeline_multichannel_long_history import run_iterated_experiment


def inspect_summary_for_seed(param: int, factor: int) -> None:
    print("================================================================")
    print(f"=== Ispezione summary long per seed (param={param}, factor={factor}) ===")
    print("================================================================")

    # Usiamo verbose=False per evitare stampe interne,
    # così vediamo solo quello che esce da questo script (se possibile).
    summary = run_iterated_experiment(
        param=param,
        factor=factor,
        iterations=10,
        spread_threshold=2.0,
        verbose=False,
    )

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
        # Attenzione: se ci sono liste molto lunghe, pprint potrebbe essere lungo,
        # ma per un primo sguardo va bene.
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
