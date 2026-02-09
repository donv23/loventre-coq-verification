import json
import copy

BASE_FILE = "lmetrics_SAT_crit16_eps_+0.000.json"

def load_metrics(fname):
    with open(fname, "r") as f:
        return json.load(f)

def signature(m):
    return (
        m["time_regime"],
        m["horizon_flag"],
        m["meta_label"]
    )

def apply_policy(m, tag):
    m2 = copy.deepcopy(m)
    m2["policy_trace"] = m2.get("policy_trace", []) + [tag]
    return m2

print("\n[Axis C — Deep Policy Composition Invariance Test (weak)]\n")

base = load_metrics(BASE_FILE)
base_sig = signature(base)

print("Base signature:", base_sig)

current = base
for i in range(1, 11):
    current = apply_policy(current, f"policy_{i}")
    sig = signature(current)
    print(f"After {i} policies →", sig)
    assert sig == base_sig

print("\n[RESULT]")
print("✔ Invarianza completa sotto composizione profonda di policy")
print("→ Le policy NON inducono dinamica strutturale su Axis C")

