"""
loventre_v42_loader.py
Loventre Engine — V42 Loader (carica ultimo V41)
Gennaio 2026

Questo modulo cerca l'ultimo JSON prodotto da V41,
lo carica come dict e lo restituisce.
"""

import os
import json


def load_latest_v41():
    """
    Cerca nell'area JSON_IO/LMetrics_v3_for_Coq
    l'ultimo file JSON che inizia con 'lmetrics_v41_rescued_'.
    """
    root = (
        "/Users/vincenzoloventre/Library/Mobile Documents/"
        "com~apple~CloudDocs/ALGORITIMIA/JSON_IO/LMetrics_v3_for_Coq"
    )

    if not os.path.exists(root):
        raise FileNotFoundError(f"[V42 Loader] Directory non trovata: {root}")

    files = sorted(
        f for f in os.listdir(root)
        if f.startswith("lmetrics_v41_rescued_") and f.endswith(".json")
    )

    if not files:
        raise FileNotFoundError("[V42 Loader] Nessun JSON V41 trovato.")

    latest = os.path.join(root, files[-1])

    with open(latest, "r", encoding="utf-8") as f:
        data = json.load(f)

    return latest, data

