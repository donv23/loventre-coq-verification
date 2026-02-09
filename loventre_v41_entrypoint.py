"""
loventre_v41_entrypoint.py
Loventre Engine — V41 LMetrics Rescue Entry
Gennaio 2026

Legge un file LMetrics (dalla cartella v3_for_Coq),
tenta un recupero strutturale e salva una versione sanata.
"""

import os
from datetime import datetime
from V41_LMETRICS_RESCUE.loventre_v41_rescue_mapper import rescue_lmetrics
from V38_LMETRICS_COQ_IMPORT.loventre_v38_coq_json_reader import load_latest_lmetrics


def save_rescued(data):
    root = (
        "/Users/vincenzoloventre/Library/Mobile Documents/"
        "com~apple~CloudDocs/ALGORITIMIA/JSON_IO/LMetrics_v3_for_Coq"
    )

    ts = datetime.now().strftime("%Y%m%d-%H%M%S")
    fname = f"lmetrics_v41_rescued_{ts}.json"

    path = os.path.join(root, fname)
    with open(path, "w", encoding="utf-8") as f:
        import json
        json.dump(data, f, indent=2)

    return path


def main():
    print("\n===== LOVENTRE ENGINE — V41 LMETRICS RESCUE =====\n")

    try:
        src = load_latest_lmetrics()
    except Exception as e:
        print("[V41] ERRORE nel caricamento:", e)
        return

    print("[V41] LMetrics RAW:", src)

    fixed = rescue_lmetrics(src)
    print("[V41] RESCUED:", fixed)

    out = save_rescued(fixed)
    print(f"\n[V41] Salvato come: {out}\n")

    print("===== END V41 LMETRICS RESCUE =====")


if __name__ == "__main__":
    main()

