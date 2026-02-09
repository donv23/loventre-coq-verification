import json
import copy

BASE_FILE = "lmetrics_SAT_crit16_eps_+0.000.json"
DELTA = 0.02

AXES = {
    "KAPPA": "kappa_eff",
    "ENTROPY": "entropy_eff",
    "CHI": "chi_compactness"
}

def decision_signature(m):
    """
    Firma minimale di decisione.
    NON calcoliamo il potenziale:
    leggiamo il regime/decisione già codificata.
    """
    return (
        m.get("decision_class"),
        m.get("time_regime"),
        m.get("horizon_flag")
    )

with open(BASE_FILE) as f:
    base = json.load(f)

base_sig = decision_signature(base)

print("\n[Axis C — Decision Jump Test]\n")
print("[BASE]", base_sig)

for axis, key in AXES.items():
    plus = copy.deepcopy(base)
    minus = copy.deepcopy(base)

    plus[key] += DELTA
    minus[key] -= DELTA

    sig_plus = decision_signature(plus)
    sig_minus = decision_signature(minus)

    print(f"\nAxis: {axis}")
    print("  minus:", sig_minus)
    print("  base :", base_sig)
    print("  plus :", sig_plus)

    if sig_minus == base_sig == sig_plus:
        print("  → decision locally flat")
    else:
        print("  → DISCRETE DECISION JUMP DETECTED")

