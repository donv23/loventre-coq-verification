"""
Loventre Engine – FULL CANONICAL DUMP TEST
Versione: dicembre 2025

Scopo:
- Stampare TUTTO ciò che il motore produce realmente
- Gestire correttamente output eterogenei (dict / str / altro)
- Nessuna assunzione sul tipo di ritorno
"""

import pprint
import traceback

from loventre_meta_engine import (
    loventre_collect_base_metrics,
    compute_barrier_diagnostic_v4,
)

SEED_GRID = [
    {"param": 1, "factor": 1},
    {"param": 1, "factor": 2},
    {"param": 1, "factor": 3},
    {"param": 2, "factor": 1},
    {"param": 2, "factor": 2},
    {"param": 2, "factor": 3},
    {"param": 3, "factor": 1},
    {"param": 3, "factor": 2},
    {"param": 3, "factor": 3},
]


def dump_any(title, obj):
    print("\n" + "-" * 80)
    print(title)
    print("-" * 80)
    print("Tipo:", type(obj))
    pprint.pprint(obj, width=120, sort_dicts=False)


def main():
    print("\n==============================")
    print(" LOVENTRE ENGINE – FULL DUMP ")
    print(" (CANONICAL, TYPE-SAFE)")
    print("==============================\n")

    for idx, seed in enumerate(SEED_GRID, start=1):
        print("\n" + "=" * 90)
        print(f"SEED #{idx}: {seed}")
        print("=" * 90)

        try:
            # ---- STADIO 1: METRICHE BASE
            base_metrics = loventre_collect_base_metrics(seed)
            dump_any("BASE METRICS", base_metrics)

            # ---- STADIO 2: DECISIONE / DIAGNOSTICA
            decision_or_metrics = compute_barrier_diagnostic_v4(base_metrics)
            dump_any("BARRIER DIAGNOSTIC OUTPUT", decision_or_metrics)

            # ---- RIASSUNTO LOGICO
            print("\n--- RIASSUNTO LOGICO ---")
            if isinstance(decision_or_metrics, dict):
                print("Output finale: METRICS BUS")
                print("Numero chiavi:", len(decision_or_metrics))
                print("Chiavi:")
                for k in decision_or_metrics.keys():
                    print(" •", k)
            else:
                print("Output finale: DECISIONE COLLASSATA")
                print("Valore:", decision_or_metrics)

        except Exception:
            print("❌ ERRORE DURANTE PIPELINE")
            traceback.print_exc()

    print("\n==============================")
    print(" FINE FULL DUMP TEST ")
    print("==============================\n")


if __name__ == "__main__":
    main()

