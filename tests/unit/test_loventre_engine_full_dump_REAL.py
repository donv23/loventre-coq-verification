"""
Loventre Engine – FULL DUMP TEST (REAL PIPELINE)
Versione: dicembre 2025

Scopo:
- Eseguire la pipeline reale del motore
- Stampare TUTTE le metriche prodotte
- Stampare output intermedi e finali
- Nessun filtro, nessuna assunzione
"""

import pprint
import traceback

from loventre_meta_engine import (
    loventre_collect_base_metrics,
    compute_barrier_diagnostic_v4,
)

# ===============================
# SEED CANONICI (griglia base)
# ===============================
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


def dump(title, obj):
    print("\n" + "-" * 80)
    print(title)
    print("-" * 80)
    pprint.pprint(obj, width=120, sort_dicts=False)


def main():
    print("\n==============================")
    print(" LOVENTRE ENGINE – FULL DUMP ")
    print(" (REAL PIPELINE)")
    print("==============================\n")

    for idx, seed in enumerate(SEED_GRID, start=1):
        print("\n" + "=" * 90)
        print(f"SEED #{idx}: {seed}")
        print("=" * 90)

        try:
            # ===============================
            # STADIO 1 — METRICHE BASE
            # ===============================
            base_metrics = loventre_collect_base_metrics(seed)

            dump("BASE METRICS (loventre_collect_base_metrics)", base_metrics)

            # ===============================
            # STADIO 2 — DIAGNOSTICA BARRIERA
            # ===============================
            full_metrics = compute_barrier_diagnostic_v4(base_metrics)

            dump("FULL METRICS (compute_barrier_diagnostic_v4)", full_metrics)

            # ===============================
            # RIASSUNTO STRUTTURALE
            # ===============================
            print("\n--- RIASSUNTO ---")
            print("Tipo output:", type(full_metrics))
            print("Numero chiavi:", len(full_metrics))
            print("Chiavi:")
            for k in full_metrics.keys():
                print(" •", k)

        except Exception:
            print("❌ ERRORE DURANTE PIPELINE")
            traceback.print_exc()

    print("\n==============================")
    print(" FINE FULL DUMP TEST ")
    print("==============================\n")


if __name__ == "__main__":
    main()

