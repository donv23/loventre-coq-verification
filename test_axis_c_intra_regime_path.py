import json
import copy

BASE_FILE = "lmetrics_SAT_crit16_eps_+0.000.json"

# piccoli passi continui
STEPS = [-0.03, -0.02, -0.01, 0.0, +0.01, +0.02, +0.03]

AXES = ["kappa_eff", "entropy_eff", "chi_compactness"]

def load_metrics(path):
    with open(path) as f:
        return json.load(f)

def signature(m):
    return (
        m.get("decision_class"),
        m.get("time_regime"),
        m.get("horizon_flag")
    )

base = load_metrics(BASE_FILE)
base_sig = signature(base)

print("\n[Axis C — Intra-Regime Path Connectedness Test]\n")
print(f"[BASE] signature = {base_sig}\n")

for axis in AXES:
    print(f"Axis: {axis}")
    connected = True

    for step in STEPS:
        m = copy.deepcopy(base)
        m[axis] = round(m[axis] + step, 5)

        sig = signature(m)

        if sig != base_sig:
            connected = False
            print(f"  ✘ break at step {step:+.3f} → signature {sig}")
            break
        else:
            print(f"  ✔ step {step:+.3f} → ok")

    if connected:
        print("  → regime internamente CONNESSO\n")
    else:
        print("  → regime internamente NON connesso\n")

print("[Axis C — Intra-Regime Path Connectedness: COMPLETATO]")

