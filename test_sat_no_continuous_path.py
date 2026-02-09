import json
import glob

print("\n[Loventre][NO-CONTINUOUS-PATH] Test di assenza di traiettorie continue\n")

FILES = sorted(glob.glob("lmetrics_SAT_crit16_eps_*.json"))

decisions = []

for f in FILES:
    with open(f) as fh:
        m = json.load(fh)

    d = (
        m["meta_label"],
        m["horizon_flag"],
        m["loventre_global_decision"]
    )
    decisions.append((f, d))
    print(f"[CHECK] {f} → {d}")

unique = set(d for _, d in decisions)

print("\n--------------------------------------------------")
if len(unique) == 1:
    print("[OK] Nessuna traiettoria continua rilevata")
    print("     Decisione costante nel regime")
    print("     Ogni uscita richiede cambio di witness")
else:
    print("[FAIL] Ambiguità dinamica rilevata (NON previsto)")
print("--------------------------------------------------\n")

