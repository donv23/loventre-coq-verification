import json
import copy

BASE_FILE = "lmetrics_SAT_crit16_eps_+0.000.json"

with open(BASE_FILE) as f:
    base = json.load(f)

def signature(m):
    return (
        m.get("decision_class"),
        m.get("time_regime"),
        m.get("horizon_flag")
    )

def perturb(m, key, delta):
    m2 = copy.deepcopy(m)
    m2[key] = round(m2[key] + delta, 5)
    return m2

print("\n[Axis C — Decision Hysteresis Test]\n")

axes = {
    "kappa_eff": "KAPPA",
    "entropy_eff": "ENTROPY",
    "chi_compactness": "CHI"
}

for key, name in axes.items():
    print(f"Axis: {name}")

    up = perturb(base, key, +0.05)
    down = perturb(up, key, -0.05)

    s_base = signature(base)
    s_up = signature(up)
    s_down = signature(down)

    print("  base:", s_base)
    print("  up  :", s_up)
    print("  down:", s_down)

    if s_down != s_base:
        print("  → HYSTERESIS DETECTED\n")
    else:
        print("  → no hysteresis\n")

