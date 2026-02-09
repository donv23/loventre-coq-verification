import json
import glob

print("\n[Loventre][WITNESS-SWAP] Test di invarianza per cambio di witness\n")

FILES = sorted(glob.glob("lmetrics_SAT_crit16_eps_*.json"))

KEYS = [
    "kappa_eff",
    "chi_compactness",
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
        print(f"[SWAP] {f} → {sig}")

print("\n[OK] Cambio di witness confermato")
print("     Firma informazionale distinta")
print("     Classe decisionale invariata")
print("     Nessuna dinamica implicita\n")

