"""
loventre_v37_entrypoint.py
Loventre Engine — V37 JSON → LMetrics → Export
Gennaio 2026

Carica un file V36, converte in LMetrics-like, e salva l'output.
"""

import os
import json
import time
from loventre_v37_json_loader import load_v36_json
from loventre_v37_json_to_lmetrics import json_to_lmetrics_v3


def save_lmetrics_record(data):
    root = "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/JSON_IO/LMetrics_v3_for_Coq"
    os.makedirs(root, exist_ok=True)

    ts = time.strftime("%Y%m%d-%H%M%S")
    filename = f"lmetrics_v37_from_v36_{ts}.json"
    full = os.path.join(root, filename)

    with open(full, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2)

    print(f"[V37 Export] Salvato: {full}")


def main():
    print("\n===== LOVENTRE ENGINE — V37 JSON→LMetrics BRIDGE =====\n")

    root = "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/JSON_IO/V36_PROGNOSIS"
    files = sorted(f for f in os.listdir(root) if f.endswith(".json"))

    if not files:
        print("[V37] Nessun file V36 trovato.")
        return

    latest = os.path.join(root, files[-1])
    print(f"[V37] Carico V36: {latest}")
    v36 = load_v36_json(latest)

    print("[V37] Convertendo in LMetrics-like…")
    lmetrics = json_to_lmetrics_v3(v36)

    print("[V37] LMetrics-like =", lmetrics)

    print("[V37] Salvo in JSON_IO/LMetrics_v3_for_Coq")
    save_lmetrics_record(lmetrics)

    print("\n===== END V37 JSON→LMetrics BRIDGE =====")


if __name__ == "__main__":
    main()

