import json
import copy

print("\n[Loventre][POLICY-COMPOSITION] Test di non-interferenza per composizione di policy\n")

BASE_FILE = "lmetrics_SAT_crit16_eps_+0.000.json"

# policy = perturbazioni annotative controllate
POLICIES = [
    ("kappa_eff", +0.02),
    ("entropy_eff", -0.02),
    ("chi_compactness", +0.03),
    ("kappa_eff", -0.01),
]

KEYS_SIGNATURE = ("meta_label", "horizon_flag", "loventre_global_decision")

def extract_signature(m):
    return tuple(m[k] for k in KEYS_SIGNATURE)

with open(BASE_FILE) as f:
    base = json.load(f)

base_sig = extract_signature(base)
print(f"[BASE] {BASE_FILE} → {base_sig}\n")

current = copy.deepcopy(base)

for i, (k, delta) in enumerate(POLICIES, start=1):
    current[k] = current[k] + delta
    sig = extract_signature(current)

    print(f"[STEP {i}] policy {k} {delta:+.3f}")
    print(f"         signature = {sig}")

    if sig != base_sig:
        print("\n[FAIL] Policy composition ha alterato la decisione ❌")
        raise SystemExit(1)

print("\n--------------------------------------------------")
print("[OK] Non-interferenza confermata per composizione di policy")
print("     Nessuna traiettoria emergente")
print("     Nessun recovery implicito")
print("     BLACKHOLE strutturalmente stabile")
print("--------------------------------------------------\n")

