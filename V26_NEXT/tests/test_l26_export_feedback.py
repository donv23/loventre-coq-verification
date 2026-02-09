import os
import json

from V26_NEXT.l26_export_feedback import (
    append_feedback_record,
    export_feedback_for_coq,
    FEEDBACK_LOG_FILE,
    FEEDBACK_DIR
)

# Assicuriamoci che NON ci sia log vecchio
if os.path.exists(FEEDBACK_LOG_FILE):
    os.remove(FEEDBACK_LOG_FILE)

# 1: prima scrittura
rec = append_feedback_record()
assert "policy" in rec
assert "signal" in rec

assert os.path.exists(FEEDBACK_LOG_FILE)
with open(FEEDBACK_LOG_FILE, "r") as f:
    log = json.load(f)
assert isinstance(log, list)
assert log[-1]["policy"] == rec["policy"]

# 2: export per Coq
out = export_feedback_for_coq()
assert os.path.exists(out)

with open(out, "r") as f:
    data = json.load(f)
assert data["policy"] == rec["policy"]
assert "timestamp" in data

print("✔ V26 EXPORT FEEDBACK OK")

