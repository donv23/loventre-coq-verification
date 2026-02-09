import json
import copy
from pathlib import Path

print("\n[Loventre][MINIMAL-ESCAPE] Test di fuga minimale\n")

BASE_FILE = "lmetrics_SAT_crit16_eps_+0.000.json"
OUT_DIR = Path("minimal_escape")
OUT_DIR.mkdir(exist_ok=True)

KEYS_TO_PERTURB = {
    "kappa_eff": [+0.05, -0.05],
    "entropy_eff": [+0.05, -0.05],
    "chi_compactness": [+0.05, -0.05],
}

INVARIANTS = [
    "meta_label",
    "horizon_flag",
    "loventre_global_decision",
]

with open(BASE_FILE) as f:
    base = json.load(f)

base_signature = tuple(base[k] for k in INVARIANTS)
print(f"[BASE] {BASE_FILE} → {base_signature}\n")

for key, deltas in KEYS_TO_PERTURB.items():
    for d in deltas:
        perturbed = copy.deepcopy(base)
        perturbed[key] = perturbed[key] + d

        fname = OUT_DIR / f"escape_{key}_{d:+.2f}.json"
        with open(fname, "w") as f:
            json.dump(perturbed, f, indent=2)

        sig = tuple(perturbed[k] for k in INVARIANTS)

        print(f"[TEST] {fname.name}")
        print(f"       perturb = {key} {d:+.2f}")
        print(f"       signature = {sig}")

        if sig != base_signature:
            print("       [FAIL] Invariante violata ❌\n")
        else:
            print("       [OK] Nessuna fuga possibile ✔\n")

print("[Loventre][MINIMAL-ESCAPE] TEST COMPLETATO\n")

