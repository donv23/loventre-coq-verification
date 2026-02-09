import os
import json

from V26_NEXT.l26_policy_feedback import (
    compute_feedback_signal,
    persist_feedback_signal,
    FEEDBACK_FILE,
    FEEDBACK_DIR
)
from V25_NEXT.l25_export_policy_history import POLICY_FILE

# Prima puliamo la memoria policy
if os.path.exists(POLICY_FILE):
    os.remove(POLICY_FILE)

# CASE 1: no policy → WAIT → 0.0
rec = compute_feedback_signal()
assert rec["policy"] == "WAIT"
assert rec["signal"] == 0.0

# CASE 2: finti log con EXPAND
os.makedirs(os.path.dirname(POLICY_FILE), exist_ok=True)
with open(POLICY_FILE, "w") as f:
    json.dump([{"timestamp":"T","policy":"EXPAND"}], f)

rec2 = compute_feedback_signal()
assert rec2["signal"] > 0

persist_feedback_signal()
assert os.path.exists(FEEDBACK_FILE)

print("✔ V26 POLICY FEEDBACK OK")

