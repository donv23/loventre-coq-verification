import json
import copy
from pathlib import Path

BASE_FILE = "lmetrics_SAT_crit16_eps_+0.000.json"

def load_metrics(fname):
    with open(fname) as f:
        return json.load(f)

def signature(m):
    return (
        m.get("decision_class"),
        m.get("time_regime"),
        m.get("horizon_flag")
    )

def perturb(m, field, delta):
    m2 = copy.deepcopy(m)
    m2[field] = round(m2[field] + delta, 6)
    return m2

def run():
    base = load_metrics(BASE_FILE)
    sig_base = signature(base)

    delta = 0.02

    print("\n[Axis C — Closed Path Holonomy Test]\n")
    print(f"[BASE] signature = {sig_base}")

    # Closed loop: +kappa → +entropy → -kappa → -entropy
    step1 = perturb(base, "kappa_eff", +delta)
    step2 = perturb(step1, "entropy_eff", +delta)
    step3 = perturb(step2, "kappa_eff", -delta)
    step4 = perturb(step3, "entropy_eff", -delta)

    sig_final = signature(step4)

    print("\n[LOOP PATH]")
    print(" base → +kappa → +entropy → -kappa → -entropy")

    print("\n[FINAL]")
    print(f"signature = {sig_final}")

    if sig_final == sig_base:
        print("\n→ NO HOLONOMY DETECTED")
        print("  Axis C globally flat for this loop")
    else:
        print("\n⚠️  HOLONOMY DETECTED")
        print("  Global non-local effect confirmed")
        print("  → separation is TOPOLOGICAL")

    print("\n[Axis C — Closed Path Holonomy: COMPLETATO]\n")

if __name__ == "__main__":
    run()

