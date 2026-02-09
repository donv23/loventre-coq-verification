import json
import math
import copy

# ----------------------------
# Configurazione
# ----------------------------

FILES = {
    "Axis_C_SAT": "lmetrics_SAT_crit16_eps_+0.000.json",
    "2SAT_crit": "metrics_2SAT_crit_demo.json",
    "3SAT_crit": "metrics_3SAT_crit_demo.json",
    "TSP_crit28": "lmetrics_TSP_crit28_example.json",
}

AXES = ["kappa_eff", "entropy_eff", "chi_compactness"]
DELTA_VALUES = [i * 0.01 for i in range(1, 31)]  # fino a 0.30

# ----------------------------
# Helpers
# ----------------------------

def load_metrics(path):
    with open(path) as f:
        return json.load(f)

def signature(m):
    return (
        m.get("decision_class"),
        m.get("time_regime"),
        m.get("horizon_flag"),
    )

def perturb(m, deltas):
    mm = copy.deepcopy(m)
    for k, v in deltas.items():
        mm[k] = mm.get(k, 0.0) + v
    return mm

# ----------------------------
# Test
# ----------------------------

print("\n[Axis C — Cross-Family Minimal Exit Distance Test]\n")

results = {}

for label, fname in FILES.items():
    base = load_metrics(fname)
    base_sig = signature(base)

    min_exit = None

    for d in DELTA_VALUES:
        # perturbazioni combinate (sfera)
        for signs in [(1,1,1), (1,1,-1), (1,-1,1), (-1,1,1),
                      (-1,-1,1), (-1,1,-1), (1,-1,-1), (-1,-1,-1)]:

            deltas = {
                AXES[i]: signs[i] * d
                for i in range(3)
            }

            test_m = perturb(base, deltas)

            if signature(test_m) != base_sig:
                min_exit = math.sqrt(3 * d * d)
                break

        if min_exit is not None:
            break

    results[label] = min_exit

# ----------------------------
# Output
# ----------------------------

print("RISULTATI (raggio minimo di uscita):\n")

for k, v in results.items():
    if v is None:
        print(f"{k:20s} → nessuna uscita rilevata (≤ {math.sqrt(3)*DELTA_VALUES[-1]:.4f})")
    else:
        print(f"{k:20s} → ||δ|| ≈ {v:.4f}")

print("\n[Axis C — Cross-Family Minimal Exit Distance: COMPLETATO]\n")

