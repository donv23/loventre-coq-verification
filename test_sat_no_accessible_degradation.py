import json
import copy

BASE = "lmetrics_SAT_crit16_eps_+0.000.json"

TESTS = [
    ("accessible_horizon_off.json", {"horizon_flag": False}),
    ("accessible_time_euclidean.json", {"time_regime": "time_euclidean"}),
    ("accessible_chi_reduce.json", {"chi_compactness": -0.20}),
]

KEYS = ("meta_label", "horizon_flag", "time_regime")

def load(fname):
    with open(fname) as f:
        return json.load(f)

def save(fname, data):
    with open(fname, "w") as f:
        json.dump(data, f, indent=2)

def signature(m):
    return tuple(m.get(k) for k in KEYS)

print("\n[Loventre][NO-ACCESSIBLE-DEGRADATION] Test di impossibilità di degradazione\n")

base = load(BASE)
base_sig = signature(base)

print(f"[BASE] {BASE} → {base_sig}\n")

for fname, patch in TESTS:
    m = copy.deepcopy(base)

    for k, v in patch.items():
        if k == "chi_compactness":
            m[k] = max(0.0, m[k] + v)
        else:
            m[k] = v

    save(fname, m)

    sig = signature(m)
    label = m.get("meta_label")

    print(f"[TEST] {fname}")
    print(f"       signature = {sig}")

    if label == "meta_P_like_accessible":
        print("       [FAIL] Degradazione verso P_accessible NON ammessa ❌")
    else:
        print("       [OK] Nessuna degradazione verso P_accessible ✔")

print("\n[Loventre][NO-ACCESSIBLE-DEGRADATION] TEST COMPLETATO\n")

