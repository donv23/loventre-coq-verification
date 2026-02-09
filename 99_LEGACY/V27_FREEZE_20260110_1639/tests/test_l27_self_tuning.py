import os, json
from V27_NEXT.l27_self_tuning import apply_self_tuning, FEEDBACK_FILE, clamp01

# setup fake feedback signals
os.makedirs(os.path.dirname(FEEDBACK_FILE), exist_ok=True)

# CASE EXPAND → +0.2
with open(FEEDBACK_FILE, "w") as f:
    json.dump({"signal":0.2,"policy":"EXPAND"}, f)

assert apply_self_tuning(0.5) == 0.7

# CASE HALT → -0.3 clamped
with open(FEEDBACK_FILE, "w") as f:
    json.dump({"signal":-0.3,"policy":"HALT"}, f)

assert apply_self_tuning(0.2) == 0.0

# CASE no file → default 0
os.remove(FEEDBACK_FILE)
assert apply_self_tuning(0.4) == 0.4

print("✔ V27 SELF TUNING OK")

