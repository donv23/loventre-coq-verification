import json
from pathlib import Path

print("\n[Loventre][DUAL-WITNESS-MIRROR] Test di mirror tra witness distinti\n")

FILES = [
    "lmetrics_SAT_crit16_eps_+0.000.json",
    "lmetrics_SAT_crit16_eps_+0.020.json",
]

KEYS = [
    "kappa_eff",
    "entropy_eff",
    "chi_compactness",
    "horizon_flag",
    "time_regime",
    "loventre_global_decision",
]

def load(fname):
    with open(fname) as f:
        return json.load(f)

def signature(m):
    return tuple(m[k] for k in KEYS)

base = load(FILES[0])
sig_base = signature(base)

print(f"[BASE] {FILES[0]} → {sig_base}")

for fname in FILES[1:]:
    m = load(fname)
    sig = signature(m)

    print(f"[MIRROR] {fname} → {sig}")

    if sig == sig_base:
        print("[FAIL] Firma identica: witness indistinguibili (non ammesso)")
        raise SystemExit(1)

print("\n--------------------------------------------------")
print("[OK] Dual witness mirror confermato")
print("     → Stessa classe decisionale")
print("     → Firma informazionale distinta")
print("     → Nessuna continuità tra witness")
print("--------------------------------------------------\n")

print("[Loventre][DUAL-WITNESS-MIRROR] TEST COMPLETATO\n")

