"""
V25 — EXPORT POLICY HISTORY
-------------------------------------
Salva la policy determinata dal motore
e la registra in un log storico, oltre
a preparare un export semplificato per Coq.
"""

import json
import os
from datetime import datetime

from V25_NEXT.l25_policy_history import compute_history_policy

POLICY_DIR = "V25_MEMORY"
POLICY_FILE = os.path.join(POLICY_DIR, "policy_log.json")

COQ_EXPORT_DIR = "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/JSON_IO/LMetrics_v3_for_Coq"
COQ_FILE = os.path.join(COQ_EXPORT_DIR, "policy_history_latest.json")

def load_policy_log():
    if not os.path.exists(POLICY_FILE):
        return []
    try:
        with open(POLICY_FILE, "r") as f:
            data = json.load(f)
        return data if isinstance(data, list) else []
    except Exception:
        return []

def append_policy_record():
    policy = compute_history_policy()
    now = datetime.utcnow().isoformat()

    log = load_policy_log()
    record = {"timestamp": now, "policy": policy}
    log.append(record)

    os.makedirs(POLICY_DIR, exist_ok=True)
    with open(POLICY_FILE, "w") as f:
        json.dump(log, f, indent=2)

    return record

def export_policy_for_coq():
    """Prende l'ultima policy e la esporta per Coq."""
    log = load_policy_log()
    if not log:
        rec = append_policy_record()
    else:
        rec = log[-1]

    minimal = {
        "policy": rec["policy"],
        "timestamp": rec["timestamp"],
    }

    os.makedirs(COQ_EXPORT_DIR, exist_ok=True)
    with open(COQ_FILE, "w") as f:
        json.dump(minimal, f, indent=2)

    return COQ_FILE

if __name__ == "__main__":
    print(export_policy_for_coq())

