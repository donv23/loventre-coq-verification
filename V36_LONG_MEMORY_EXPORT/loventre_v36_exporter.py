"""
loventre_v36_exporter.py
Loventre Engine — V36 JSON Memory Export
Gennaio 2026

Questo modulo prende l'esito V35 (classifier + prognosis)
e lo congela in un file JSON canonico in JSON_IO/V36_PROGNOSIS/.
"""

import json
import os
from datetime import datetime
from pathlib import Path


def export_v36_prognosis(classifier, prognosis, extra=None):
    """
    Salva classifier + prognosis + eventuali extra in un JSON timestamped.

    Ritorna il path (stringa) del file creato.
    """
    root = Path(
        "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/"
        "ALGORITIMIA/JSON_IO/V36_PROGNOSIS"
    )
    root.mkdir(parents=True, exist_ok=True)

    timestamp = datetime.utcnow().strftime("%Y%m%d-%H%M%S")
    filename = f"loventre_v36_prognosis_{timestamp}.json"
    filepath = root / filename

    payload = {
        "timestamp_utc": timestamp,
        "classifier": classifier,
        "prognosis": prognosis,
    }

    if extra:
        payload["extra"] = extra

    with open(filepath, "w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2, ensure_ascii=False)

    return str(filepath)

