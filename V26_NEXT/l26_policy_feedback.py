"""
V26 — POLICY FEEDBACK LOOP
--------------------------------
Traduce la policy storica in un segnale
che può modulare il comportamento futuro
del motore.
"""

import os
import json

from V25_NEXT.l25_export_policy_history import load_policy_log

FEEDBACK_DIR = "V26_MEMORY"
FEEDBACK_FILE = os.path.join(FEEDBACK_DIR, "feedback_signal.json")

def compute_feedback_signal():
    log = load_policy_log()
    if not log:
        return {"signal": 0.0, "policy": "WAIT"}

    last = log[-1]
    pol = last.get("policy", "WAIT")

    if pol == "EXPAND":
        sig = 0.2     # incrementa esplorazione
    elif pol == "HALT":
        sig = -0.3    # frena
    elif pol == "STABILIZE":
        sig = 0.0     # nessuna variazione
    else:
        sig = 0.0     # WAIT o ignoto

    return {"signal": sig, "policy": pol}

def persist_feedback_signal():
    rec = compute_feedback_signal()
    os.makedirs(FEEDBACK_DIR, exist_ok=True)
    with open(FEEDBACK_FILE, "w") as f:
        json.dump(rec, f, indent=2)
    return rec

if __name__ == "__main__":
    print(persist_feedback_signal())

