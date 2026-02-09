"""
L24 EXPORT TOP FOR COQ (V24)
------------------------------------
Prende i top-K ricordi e li esporta
in formato semplificato adatto a Coq.
"""

import json
import os
from V24_NEXT.l24_memory_ranking import rank_memory_top_k, MEMORY_DIR

COQ_EXPORT_DIR = "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/JSON_IO/LMetrics_v3_for_Coq"

def minimal_projection(item):
    """Riduci solo ai campi utili al ponte Coq."""
    return {
        "state": item.get("state"),
        "weight": item.get("weight"),
        "kind": item.get("kind", "UNKNOWN"),
        "trend": item.get("trend", None),
    }

def export_top_k_for_coq(k=5):
    mem = rank_memory_top_k(k)
    proj = [minimal_projection(x) for x in mem]

    os.makedirs(COQ_EXPORT_DIR, exist_ok=True)
    out_file = os.path.join(COQ_EXPORT_DIR, f"memory_top_{k}_for_coq.json")

    with open(out_file, "w") as f:
        json.dump(proj, f, indent=2)

    return out_file

if __name__ == "__main__":
    print(export_top_k_for_coq(5))

