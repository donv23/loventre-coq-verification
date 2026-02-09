import os
import json

from V25_NEXT.l25_policy_history import compute_history_policy, MEMORY_FILE, MEMORY_DIR

os.makedirs(MEMORY_DIR, exist_ok=True)

def write(mem):
    with open(MEMORY_FILE, "w") as f:
        json.dump(mem, f)

# CASE 1: empty → WAIT
write([])
assert compute_history_policy() == "WAIT"

# CASE 2: SAFE dominates → EXPAND
write([
    {"kind": "SAFE", "weight": 0.9},
    {"kind": "SAFE_ACCESSIBLE", "weight": 0.7}
])
assert compute_history_policy() == "EXPAND"

# CASE 3: BH majority → HALT
write([
    {"kind": "BLACKHOLE", "weight": 1.0},
    {"kind": "BLACKHOLE", "weight": 0.9},
    {"kind": "SAFE", "weight": 0.1},
])
assert compute_history_policy() == "HALT"

# CASE 4: balanced → STABILIZE
write([
    {"kind": "SAFE", "weight": 1.0},
    {"kind": "BLACKHOLE", "weight": 1.0},
])
assert compute_history_policy() == "STABILIZE"

print("✔ V25 POLICY HISTORY OK")

