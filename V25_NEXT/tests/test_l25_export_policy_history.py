import os
import json

from V25_NEXT.l25_export_policy_history import (
    append_policy_record,
    export_policy_for_coq,
    POLICY_FILE,
    POLICY_DIR,
    COQ_EXPORT_DIR
)

# Pulisci eventuali vecchi file
if os.path.exists(POLICY_FILE):
    os.remove(POLICY_FILE)

# 1) append policy
rec = append_policy_record()
assert "policy" in rec
assert "timestamp" in rec

# 2) file log deve esistere ed essere lista
assert os.path.exists(POLICY_FILE)
with open(POLICY_FILE, "r") as f:
    data = json.load(f)
assert isinstance(data, list)
assert data[-1]["policy"] == rec["policy"]

# 3) export per Coq
out = export_policy_for_coq()
assert os.path.exists(out)

with open(out, "r") as f:
    exported = json.load(f)

assert exported["policy"] == rec["policy"]
assert "timestamp" in exported

print("✔ V25 EXPORT POLICY HISTORY OK")

