"""
V24 — Weighted Memory Layer
Assegna un peso all'osservazione corrente
e la scrive in una memoria dedicata.
"""

import os
import json

V24_MEMORY_FILE = os.path.join("V24_MEMORY", "weighted_memory.json")

def compute_weighted_importance(snapshot):
    raw = snapshot.get("raw_value", 0.0)
    entropy = snapshot.get("entropy", 0.0)
    state = snapshot.get("decision_state", "UNKNOWN")

    if state == "SAFE_ACCESSIBLE":
        bonus = 0.5
    elif state == "SAFE":
        bonus = 0.2
    elif state == "BLACKHOLE":
        bonus = 1.0
    else:
        bonus = 0.0

    weight = (1 - entropy) * (1 + bonus)
    return max(0.0, min(weight, 2.0))

def append_weighted_memory(snapshot):
    os.makedirs("V24_MEMORY", exist_ok=True)

    data = []
    if os.path.exists(V24_MEMORY_FILE):
        try:
            with open(V24_MEMORY_FILE, "r") as f:
                data = json.load(f)
        except:
            data = []

    entry = {
        "raw_value": snapshot.get("raw_value", 0.0),
        "entropy": snapshot.get("entropy", 0.0),
        "decision_state": snapshot.get("decision_state", "UNKNOWN"),
        "weight": compute_weighted_importance(snapshot)
    }

    data.append(entry)

    with open(V24_MEMORY_FILE, "w") as f:
        json.dump(data, f, indent=2)

    return entry

