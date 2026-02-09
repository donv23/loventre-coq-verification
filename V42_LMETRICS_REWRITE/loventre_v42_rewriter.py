"""
loventre_v42_rewriter.py
Loventre Engine — V42 Rewriter
Gennaio 2026

Prende un LMetrics dict riparato da V41
e lo installa come nuovo policy_history_latest.json
"""

import json
import shutil
import os
from datetime import datetime


def rewrite_policy_latest(v41_path, v41_dict):
    """
    Salva il dict passato come policy_history_latest.json
    e ne mantiene una copia timestampata.
    """
    root = (
        "/Users/vincenzoloventre/Library/Mobile Documents/"
        "com~apple~CloudDocs/ALGORITIMIA/JSON_IO/LMetrics_v3_for_Coq"
    )

    if not os.path.exists(root):
        raise FileNotFoundError(f"[V42 Rewriter] Directory non trovata: {root}")

    # Nuova destinazione canonica
    latest_path = os.path.join(root, "policy_history_latest.json")

    # Backup del vecchio
    if os.path.exists(latest_path):
        ts = datetime.now().strftime("%Y%m%d-%H%M%S")
        backup = os.path.join(root, f"policy_backup_before_v42_{ts}.json")
        shutil.copy2(latest_path, backup)

    # Scrivi nuova versione ufficiale
    with open(latest_path, "w", encoding="utf-8") as f:
        json.dump(v41_dict, f, indent=2)

    # Copia timestampata del rescued
    ts_file = datetime.now().strftime("%Y%m%d-%H%M%S")
    promoted = os.path.join(root, f"lmetrics_v42_promoted_{ts_file}.json")
    with open(promoted, "w", encoding="utf-8") as f:
        json.dump(v41_dict, f, indent=2)

    return latest_path, promoted

