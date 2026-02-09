import json
import copy
import os

BASE_FILE = "lmetrics_SAT_crit16_eps_+0.000.json"
DELTA = 0.02

AXES = [
    ("kappa_eff", "KAPPA"),
    ("entropy_eff", "ENTROPY"),
    ("chi_compactness", "CHI"),
]

OUT_DIR = "axis_c_anisotropy_results"
os.makedirs(OUT_DIR, exist_ok=True)

def load_json(path):
    with open(path, "r") as f:
        return json.load(f)

def save_json(obj, path):
    with open(path, "w") as f:
        json.dump(obj, f, indent=2)

base = load_json(BASE_FILE)

results = []

for field, label in AXES:
    for sign in [+1, -1]:
        perturbed = copy.deepcopy(base)
        perturbed[field] = round(perturbed[field] + sign * DELTA, 6)

        tag = f"{label}_{'PLUS' if sign > 0 else 'MINUS'}"
        out_name = f"{OUT_DIR}/anisotropy_{tag}.json"

        save_json(perturbed, out_name)

        summary = {
            "axis": label,
            "direction": "+" if sign > 0 else "-",
            "kappa_eff": perturbed.get("kappa_eff"),
            "entropy_eff": perturbed.get("entropy_eff"),
            "chi_compactness": perturbed.get("chi_compactness"),
            "decision_class": perturbed.get("decision_class"),
            "time_regime": perturbed.get("time_regime"),
        }

        results.append(summary)

print("\n[Axis C — Anisotropy Test Results]\n")
for r in results:
    print(r)

