"""
loventre_v38_lmetrics_export.py
Loventre Engine — V38 Export LMetrics dict to Coq-friendly JSON
Gennaio 2026

Scrive un file JSON pronto per Coq (non converte strutture).
"""

import json
import os
from datetime import datetime


def export_lmetrics_for_coq(lmetrics_dict):
    """
    Salva il dict in JSON_IO/LMetrics_v3_for_Coq/lmetrics_v38_export_<timestamp>.json
    """
    root = "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/JSON_IO/LMetrics_v3_for_Coq"

    os.makedirs(root, exist_ok=True)

    stamp = datetime.now().strftime("%Y%m%d-%H%M%S")
    outpath = os.path.join(root, f"lmetrics_v38_export_{stamp}.json")

    with open(outpath, "w", encoding="utf-8") as f:
        json.dump(lmetrics_dict, f, indent=2, ensure_ascii=False)

    return outpath

