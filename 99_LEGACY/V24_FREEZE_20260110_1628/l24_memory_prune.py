"""
L24 MEMORY PRUNE (V24)
------------------------------------
Rimuove i ricordi meno significativi
mantenendo solo un massimo di N elementi.
"""

import json
import os

MEMORY_DIR = "V24_MEMORY"
MEMORY_FILE = os.path.join(MEMORY_DIR, "weighted_memory.json")

def load_memory():
    if not os.path.exists(MEMORY_FILE):
        return []
    try:
        with open(MEMORY_FILE, "r") as f:
            data = json.load(f)
        if isinstance(data, list):
            return data
        return []
    except Exception:
        return []

def prune_memory(max_items=100):
    mem = load_memory()
    # ordina dal più pesante al più leggero
    ranked = sorted(mem, key=lambda x: x.get("weight", 0), reverse=True)
    pruned = ranked[:max_items]
    return pruned

def apply_prune(max_items=100):
    pruned = prune_memory(max_items)
    os.makedirs(MEMORY_DIR, exist_ok=True)
    with open(MEMORY_FILE, "w") as f:
        json.dump(pruned, f, indent=2)
    return len(pruned)

if __name__ == "__main__":
    print(apply_prune(100))

