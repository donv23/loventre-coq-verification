"""
loventre_v38_coq_json_reader.py
Loventre Engine — V38 LMetrics JSON Reader for Coq
Gennaio 2026

Legge un file JSON V37 (LMetrics-like) ed esporta il dict.
Non assume semantica sui campi.
"""

import json
import os


def load_latest_lmetrics():
    """
    Cerca nella cartella JSON_IO/LMetrics_v3_for_Coq
    e carica l'ultimo file .json.
    """
    root = "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/JSON_IO/LMetrics_v3_for_Coq"

    if not os.path.exists(root):
        raise FileNotFoundError(f"[V38] Directory non trovata: {root}")

    files = sorted(f for f in os.listdir(root) if f.endswith(".json"))
    if not files:
        raise FileNotFoundError("[V38] Nessun file LMetrics V37 trovato.")

    latest = os.path.join(root, files[-1])

    with open(latest, "r", encoding="utf-8") as f:
        data = json.load(f)

    return latest, data

