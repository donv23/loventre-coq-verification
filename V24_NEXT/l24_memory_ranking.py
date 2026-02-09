"""
L24 MEMORY RANKING (V24)
------------------------------------
Ordina la memoria pesata e restituisce i Top-K
"""

import json
import os

MEMORY_DIR = "V24_MEMORY"
MEMORY_FILE = os.path.join(MEMORY_DIR, "weighted_memory.json")

def get_weighted_memory():
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

def rank_memory_top_k(k=5):
    mem = get_weighted_memory()
    # ordina in base al peso
    ranked = sorted(mem, key=lambda x: x.get("weight", 0), reverse=True)
    return ranked[:k]

def export_ranked_top_k(k=5):
    ranked = rank_memory_top_k(k)
    out_file = os.path.join(MEMORY_DIR, f"memory_top_{k}.json")
    with open(out_file, "w") as f:
        json.dump(ranked, f, indent=2)
    return out_file

if __name__ == "__main__":
    print(export_ranked_top_k(5))

