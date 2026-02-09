"""
loventre_v38_entrypoint.py
Loventre Engine — V38 COQ Import Step
Gennaio 2026

Carica ultimo LMetrics V37 e lo risalva come V38 ready-for-Coq.
"""

from V38_LMETRICS_COQ_IMPORT.loventre_v38_coq_json_reader import load_latest_lmetrics
from V38_LMETRICS_COQ_IMPORT.loventre_v38_lmetrics_export import export_lmetrics_for_coq


def main():
    print("\n===== LOVENTRE ENGINE — V38 COQ IMPORT =====\n")

    try:
        src, lm = load_latest_lmetrics()
        print(f"[V38] Caricato: {src}")
    except Exception as e:
        print(f"[V38 ERROR] {e}")
        return

    print("[V38] LMetrics dict:", lm)

    target = export_lmetrics_for_coq(lm)
    print(f"[V38] Esportato come: {target}")

    print("\n===== END V38 COQ IMPORT =====")


if __name__ == "__main__":
    main()

