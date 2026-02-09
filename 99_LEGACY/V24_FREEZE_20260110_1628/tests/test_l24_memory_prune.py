import os
import json

from V24_NEXT.l24_memory_prune import prune_memory, apply_prune, MEMORY_FILE, MEMORY_DIR

os.makedirs(MEMORY_DIR, exist_ok=True)

# genera un weighted_memory con 6 ricordi
fake = [
    {"state": "S1", "weight": 0.9},
    {"state": "S2", "weight": 0.5},
    {"state": "S3", "weight": 0.1},
    {"state": "S4", "weight": 0.8},
    {"state": "S5", "weight": 0.05},
    {"state": "S6", "weight": 0.3},
]

with open(MEMORY_FILE, "w") as f:
    json.dump(fake, f)

# 1) prune a 3 elementi
p3 = prune_memory(3)
assert len(p3) == 3
assert p3[0]["state"] == "S1"
assert p3[1]["state"] == "S4"
assert p3[2]["state"] == "S2"

# 2) applica pruning a 4
apply_prune(4)
with open(MEMORY_FILE, "r") as f:
    saved = json.load(f)
assert len(saved) == 4

print("✔ V24 MEMORY PRUNE OK")

