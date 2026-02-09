import json
from pathlib import Path

# --------------------------------------------------
# Axis C — Discrete Witness Mutation Invariance Test
# --------------------------------------------------

SAT_WITNESS_FILES = [
    "lmetrics_SAT_crit16_eps_+0.000.json",
    "lmetrics_SAT_crit16_eps_+0.005.json",
    "lmetrics_SAT_crit16_eps_-0.005.json",
    "lmetrics_SAT_crit16_eps_+0.010.json",
    "lmetrics_SAT_crit16_eps_-0.010.json",
    "lmetrics_SAT_crit16_eps_+0.020.json",
]

def load_signature(path):
    with open(path) as f:
        data = json.load(f)

    return (
        data.get("decision_class"),
        data.get("time_regime"),
        data.get("horizon_flag"),
    )

def run():
    print("\n[Axis C — Discrete Witness Mutation Invariance Test]\n")

    signatures = {}

    for fname in SAT_WITNESS_FILES:
        path = Path(fname)
        if not path.exists():
            print(f"[SKIP] {fname} non trovato")
            continue

        sig = load_signature(path)
        signatures[fname] = sig

        print(f"{fname:40s} → signature = {sig}")

    print("\n[STRUCTURAL CHECK]\n")

    unique_signatures = set(signatures.values())

    if len(unique_signatures) == 1:
        print("[OK ] Invarianza confermata")
        print("     → Regime Axis C indipendente dal witness SAT")
        print("     → Nessuna dipendenza rappresentazionale interna alla famiglia")
    else:
        print("[FAIL] Invarianza violata")
        print("       Firme distinte rilevate:")
        for sig in unique_signatures:
            print("       ", sig)

    print("\n[Axis C — Witness Mutation Invariance: COMPLETATO]\n")

if __name__ == "__main__":
    run()

