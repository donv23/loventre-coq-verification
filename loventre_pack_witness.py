"""
LOVENTRE ENGINE — PACK WITNESS FOR COQ
Raccoglie tutti i JSON_IO/WITNESS
e crea:
- WITNESS_PACK.json        (lista completa)
- WITNESS_SUMMARY.json     (contatori e timestamp)
"""

import json
import os
from datetime import datetime

WIT_DIR = "JSON_IO/WITNESS"
OUT_PACK = "JSON_IO/WITNESS_PACK.json"
OUT_SUMMARY = "JSON_IO/WITNESS_SUMMARY.json"

def main():
    files = sorted(os.listdir(WIT_DIR))
    data = []
    counts = {"SAFE": 0, "ACCESS": 0, "BH": 0}

    for f in files:
        path = os.path.join(WIT_DIR, f)
        with open(path) as fh:
            obj = json.load(fh)
            label = "SAFE"
            if "ACCESS" in f:
                label = "ACCESS"
            if "BH" in f:
                label = "BH"
            counts[label] += 1
            data.append({"label": label, "point": obj, "file": f})

    with open(OUT_PACK, "w") as f:
        json.dump(data, f, indent=2)

    with open(OUT_SUMMARY, "w") as f:
        json.dump({
            "timestamp": datetime.utcnow().isoformat(),
            "counts": counts,
            "total": len(files)
        }, f, indent=2)

    print("📦 PACK READY:")
    print(f" - {OUT_PACK}")
    print(f" - {OUT_SUMMARY}")
    print(counts)

if __name__ == "__main__":
    main()

