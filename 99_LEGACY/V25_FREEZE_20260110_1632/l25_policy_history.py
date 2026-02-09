"""
V25 — HISTORY DRIVEN POLICY
-------------------------------------
Legge la memoria potata e deduce una policy evolutiva.
"""

import json
import os

MEMORY_DIR = "V24_MEMORY"
MEMORY_FILE = os.path.join(MEMORY_DIR, "weighted_memory.json")

def load_pruned_memory():
    if not os.path.exists(MEMORY_FILE):
        return []
    try:
        with open(MEMORY_FILE, "r") as f:
            data = json.load(f)
        return data if isinstance(data, list) else []
    except Exception:
        return []

def compute_history_policy():
    mem = load_pruned_memory()
    if not mem:
        return "WAIT"

    total = len(mem)
    bh = sum(1 for x in mem if x.get("kind") == "BLACKHOLE")
    safe = sum(1 for x in mem if x.get("kind") == "SAFE")
    acc = sum(1 for x in mem if x.get("kind") == "SAFE_ACCESSIBLE")

    # Rule set V25 (risolto pareggio!)
    if bh / total > 0.5:
        return "HALT"
    if (safe + acc) > bh:
        return "EXPAND"
    return "STABILIZE"

if __name__ == "__main__":
    print(compute_history_policy())

