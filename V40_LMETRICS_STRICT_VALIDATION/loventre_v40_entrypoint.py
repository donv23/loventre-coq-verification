"""
loventre_v40_entrypoint.py
Loventre Engine — V40 Strict LMetrics Validator + Cleaner + Export
Gennaio 2026

Pipeline:
  1. Carica ultimo JSON V37/V38 da JSON_IO/LMetrics_v3_for_Coq
  2. Valida secondo schema minimo
  3. Se valido -> pulisci e salva lmetrics_v40_clean.json
  4. Se non valido -> stampa errori e NON salva
"""

import os
import json
from datetime import datetime

from loventre_v40_validator import validate_lmetrics
from loventre_v40_cleaner import clean_lmetrics


def load_latest_lmetrics():
    """
    Cerca l'ultimo JSON nella cartella LMetrics_v3_for_Coq.
    """
    root = "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/JSON_IO/LMetrics_v3_for_Coq"
    files = sorted(f for f in os.listdir(root) if f.endswith(".json"))
    if not files:
        raise FileNotFoundError("[V40] Nessun file LMetrics trovato.")
    return os.path.join(root, files[-1])


def main():
    print("\n===== LOVENTRE ENGINE — V40 STRICT VALIDATION =====\n")

    # 1. Carica file
    try:
        path = load_latest_lmetrics()
    except Exception as e:
        print("[V40] ERRORE caricamento:", e)
        return

    print(f"[V40] Carico: {path}")

    with open(path, "r", encoding="utf-8") as f:
        data = json.load(f)

    print("[V40] Contenuto raw:", data)

    # 2. Valida
    ok, errors = validate_lmetrics(data)
    if not ok:
        print("\n[V40] VALIDAZIONE FALLITA ❌")
        for err in errors:
            print("   -", err)
        print("\n[V40] Nessun file generato.\n")
        return

    print("\n[V40] VALIDAZIONE OK ✔️")

    # 3. Clean
    cleaned = clean_lmetrics(data)
    if cleaned is None:
        print("[V40] Clean fallito (chiavi mancanti). Nessun file scritto.")
        return

    # 4. Scrivi file pulito
    now = datetime.now().strftime("%Y%m%d-%H%M%S")
    out_root = "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/JSON_IO/LMetrics_v3_for_Coq"
    out_path = os.path.join(out_root, f"lmetrics_v40_clean_{now}.json")

    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(cleaned, f, indent=2)

    print(f"\n[V40] Salvato come: {out_path}")

    print("\n===== END V40 STRICT VALIDATION =====\n")


if __name__ == "__main__":
    main()

