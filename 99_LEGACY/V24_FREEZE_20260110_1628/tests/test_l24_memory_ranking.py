import os
import json

from V24_NEXT.l24_memory_ranking import rank_memory_top_k, export_ranked_top_k, MEMORY_DIR

# Prepara un finto weighted_memory.json per il test
os.makedirs(MEMORY_DIR, exist_ok=True)
TEST_FILE = os.path.join(MEMORY_DIR, "weighted_memory.json")

fake_data = [
    {"state": "S1", "weight": 0.2},
    {"state": "S2", "weight": 0.9},
    {"state": "S3", "weight": 0.5},
    {"state": "S4", "weight": 0.7},
]

with open(TEST_FILE, "w") as f:
    json.dump(fake_data, f)

# Test 1: ranking base
top3 = rank_memory_top_k(3)
assert len(top3) == 3
assert top3[0]["state"] == "S2"
assert top3[1]["state"] == "S4"
assert top3[2]["state"] == "S3"

# Test 2: export
out = export_ranked_top_k(2)
assert os.path.exists(out)
with open(out, "r") as f:
    exported = json.load(f)
assert exported[0]["state"] == "S2"
assert exported[1]["state"] == "S4"

print("✔ V24 MEMORY RANKING OK")

