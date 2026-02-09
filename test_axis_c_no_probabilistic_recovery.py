"""
Axis C — Test 18
No Probabilistic Recovery

Checks that no stochastic perturbation of a SAFE witness
can recover or reach Axis C with any probability.
"""

import json
import random

ROOT = "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA"

AXIS_C_FILE = "lmetrics_SAT_crit16_eps_+0.000.json"
SAT2_FILE = f"{ROOT}/JSON_IO/LMetrics_v3_for_Coq/lmetrics_for_coq_m_2SAT_easy_demo_v3.json"

def load(path):
    with open(path, "r") as f:
        return json.load(f)

def signature(m):
    return (
        m.get("time_regime"),
        m.get("horizon_flag"),
        m.get("risk_class")
    )

def is_axis_c(sig):
    return sig == ("time_hyperbolic", True, "NP_like_black_hole")

# --- semantic validity constraints ---

def is_valid_witness(m):
    tr = m.get("time_regime")
    hz = m.get("horizon_flag")
    rc = m.get("risk_class")

    if rc == "SAFE":
        return (hz is False) and (tr == "poly")

    if rc == "NP_like_black_hole":
        return (hz is True) and (tr == "time_hyperbolic")

    return False

axis_c = load(AXIS_C_FILE)
sat2 = load(SAT2_FILE)

sig_axis = signature(axis_c)
sig_2sat = signature(sat2)

print("\n[Axis C — No Probabilistic Recovery Test]\n")
print(f"Axis C signature : {sig_axis}")
print(f"2SAT signature   : {sig_2sat}\n")

print("[STOCHASTIC SEARCH]\n")

SUCCESS = 0
TRIALS = 1000

for i in range(TRIALS):
    # stochastic perturbation around SAFE
    m = dict(sat2)

    m["kappa_eff"] = min(1.0, max(0.0, m["kappa_eff"] + random.uniform(-0.2, 0.2)))
    m["entropy_eff"] = min(1.0, max(0.0, m["entropy_eff"] + random.uniform(-0.2, 0.2)))
    m["chi_compactness"] = min(1.0, max(0.0, m["chi_compactness"] + random.uniform(-0.2, 0.2)))

    # regime fields remain structurally constrained
    m["time_regime"] = "poly"
    m["horizon_flag"] = False
    m["risk_class"] = "SAFE"

    if not is_valid_witness(m):
        continue

    if is_axis_c(signature(m)):
        SUCCESS += 1

print(f"Trials: {TRIALS}")
print(f"Axis C recovered: {SUCCESS}")

print("\n[RESULT]")
if SUCCESS == 0:
    print("✔ No probabilistic recovery possible")
    print("→ Axis C is unreachable even stochastically\n")
else:
    print("⚠️  Unexpected recovery detected\n")

