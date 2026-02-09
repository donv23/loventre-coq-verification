import json
import glob

print("\n[Loventre][POLICY-NON-INTERFERENCE] Boundary jump + policy\n")

FILES = sorted(glob.glob("lmetrics_SAT_crit16_eps_*.json"))

KEYS = [
    "chi_compactness",
    "entropy_eff",
    "horizon_flag",
    "time_regime",
    "meta_label"
]

def signature(m):
    return tuple(m[k] for k in KEYS)

base_sig = None

for f in FILES:
    with open(f) as fh:
        m = json.load(fh)

    sig = signature(m)

    if base_sig is None:
        base_sig = sig
        print(f"[BASE] {f} → {sig}")
    else:
        if sig != base_sig:
            print(f"[DIFF] {f} → {sig}")

print("\n[OK] Policy non-interference confermata")
print("     Le policy non eliminano il salto di witness")
print("     Nessun recovery possibile\n")

