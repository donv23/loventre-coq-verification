"""
loventre_v37_json_loader.py
Loventre Engine — V37 JSON Loader
Gennaio 2026

Legge un file JSON V36 e ritorna un dict Python.
Non assume nulla sulla semantica dei campi.
"""

import json
import os


def load_v36_json(filepath):
    """
    Carica un file V36 (prognosis) e lo ritorna come dict.
    Se il file non esiste, lancia FileNotFoundError.
    """
    if not os.path.exists(filepath):
        raise FileNotFoundError(f"[V37] File non trovato: {filepath}")

    with open(filepath, "r", encoding="utf-8") as f:
        data = json.load(f)

    return data


def main():
    # Dimostrazione: carica l'ultimo file nella cartella V36_PROGNOSIS
    root = "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/JSON_IO/V36_PROGNOSIS"
    files = sorted(
        f for f in os.listdir(root) if f.endswith(".json")
    )
    if not files:
        print("[V37 JSON Loader] Nessun file V36 trovato.")
        return

    latest = os.path.join(root, files[-1])
    print(f"[V37 JSON Loader] Carico: {latest}")
    data = load_v36_json(latest)
    print("[V37 JSON Loader] Contenuto:", data)


if __name__ == "__main__":
    main()

