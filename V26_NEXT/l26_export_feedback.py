"""
V26 — EXPORT FEEDBACK
-------------------------------------
Scrive il feedback della policy in un log
e produce un JSON semplificato per Coq.
"""

import os
import json

from datetime import datetime

from V26_NEXT.l26_policy_feedback import compute_feedback_signal, FEEDBACK_DIR

FEEDBACK_LOG_FILE = os.path.join(FEEDBACK_DIR, "feedback_log.json")

COQ_EXPORT_DIR = "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/JSON_IO/LMetrics_v3_for_Coq"
COQ_FILE = os.path.join(COQ_EXPORT_DIR, "feedback_latest.json")

def load_feedback_log():
    if not os.path.exists(FEEDBACK_LOG_FILE):
        return []
    try:
        with open(FEEDBACK_LOG_FILE, "r") as f:
            data = json.load(f)
        return data if isinstance(data, list) else []
    except Exception:
        return []

def append_feedback_record():
    sig = compute_feedback_signal()
    now = datetime.utcnow().isoformat()

    log = load_feedback_log()
    record = {
        "timestamp": now,
        "policy": sig["policy"],
        "signal": sig["signal"]
    }
    log.append(record)

    os.makedirs(FEEDBACK_DIR, exist_ok=True)
    with open(FEEDBACK_LOG_FILE, "w") as f:
        json.dump(log, f, indent=2)

    return record

def export_feedback_for_coq():
    rec = append_feedback_record()

    minimal = {
        "policy": rec["policy"],
        "signal": rec["signal"],
        "timestamp": rec["timestamp"]
    }

    os.makedirs(COQ_EXPORT_DIR, exist_ok=True)
    with open(COQ_FILE, "w") as f:
        json.dump(minimal, f, indent=2)

    return COQ_FILE

if __name__ == "__main__":
    print(export_feedback_for_coq())

