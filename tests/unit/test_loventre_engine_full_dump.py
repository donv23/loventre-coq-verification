"""
Loventre Engine – FULL DUMP TEST
Versione: dicembre 2025

Scopo:
- Eseguire il motore su tutti i seed base
- Stampare TUTTE le metriche prodotte
- Mostrare struttura completa del metrics bus
- Nessun filtro, nessuna semplificazione
"""

import json
import pprint
import traceback

# ===============================
# IMPORT MOTORE
# ===============================
try:
    from loventre_meta_engine import meta_decide_instance_with_mass
except Exception as e:
    print("❌ ERRORE IMPORT MOTORE")
    raise e


# ===============================
# SEED DI TEST (griglia canonica)
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


def pretty_print_metrics(metrics):
    """
    Stampa leggibile + dump JSON
    """
    print("\n--- METRICS BUS (pretty) ---")
    pprint.pprint(metrics, width=120, sort_dicts=False)

    print("\n--- METRICS BUS (JSON) ---")
    try:
        print(json.dumps(metrics, indent=2, default=str))
    except Exception:
        print("⚠️ Impossibile serializzare in JSON puro")


def main():
    print("\n==============================")
    print(" LOVENTRE ENGINE – FULL DUMP ")
    print("==============================\n")

    for idx, seed in enumerate(SEED_GRID, start=1):
        print("\n" + "=" * 80)
        print(f"SEED #{idx}: {seed}")
        print("=" * 80)

        try:
            metrics = meta_decide_instance_with_mass(seed)
        except Exception as e:
            print("❌ ERRORE DURANTE ESECUZIONE MOTORE")
            traceback.print_exc()
            continue

        print("\n✔ MOTORE ESEGUITO")
        print(f"Tipo metrics: {type(metrics)}")
        print(f"Numero chiavi: {len(metrics)}")

        print("\n--- ELENCO CHIAVI ---")
        for k in metrics.keys():
            print(" •", k)

        # Dump totale
        pretty_print_metrics(metrics)

    print("\n==============================")
    print(" FINE FULL DUMP TEST ")
    print("==============================\n")


if __name__ == "__main__":
    main()

