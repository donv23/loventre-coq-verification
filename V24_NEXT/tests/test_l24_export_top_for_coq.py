import os
import json

from V24_NEXT.l24_export_top_for_coq import export_top_k_for_coq, COQ_EXPORT_DIR
from V24_NEXT.l24_memory_ranking import MEMORY_DIR, MEMORY_FILE

# Prepara memoria sintetica
os.makedirs(MEMORY_DIR, exist_ok=True)
fake = [
    {"state": "A", "weight": 1.0, "kind": "SAFE"},
    {"state": "B", "weight": 0.5, "kind": "SAFE_ACCESSIBLE"},
    {"state": "C", "weight": 0.1, "kind": "BH"},
]
with open(MEMORY_FILE, "w") as f:
    json.dump(fake, f)

out = export_top_k_for_coq(2)
assert os.path.exists(out)

with open(out, "r") as f:
    data = json.load(f)

assert len(data) == 2
assert data[0]["state"] == "A"
assert "weight" in data[0]
assert "kind" in data[0]

print("✔ V24 EXPORT TOP FOR COQ OK")

