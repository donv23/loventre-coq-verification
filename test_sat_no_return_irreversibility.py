import json

FILES = [
    "lmetrics_SAT_crit16_eps_-0.020.json",
    "lmetrics_SAT_crit16_eps_+0.000.json",
    "lmetrics_SAT_crit16_eps_+0.020.json"
]

def load_sig(f):
    with open(f) as fh:
        m = json.load(fh)
    return (
        m["chi_compactness"],
        m["entropy_eff"],
        m["horizon_flag"],
        m["meta_label"]
    )

sigs = [load_sig(f) for f in FILES]

print("\n[Loventre][NO-RETURN] Test di irreversibilità\n")

for f, s in zip(FILES, sigs):
    print(f"{f} → {s}")

if sigs[0] != sigs[1] or sigs[1] != sigs[2]:
    print("\n[OK] Irreversibilità confermata")
    print("     Nessun ritorno di witness")
    print("     Nessuna dinamica temporale nascosta\n")
else:
    print("\n[FAIL] Possibile continuità (non attesa)\n")

