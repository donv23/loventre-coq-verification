import json
import math
from itertools import combinations

FILES = {
    "SAT_crit": "lmetrics_SAT_crit16_eps_+0.000.json",
    "3SAT_crit": "metrics_3SAT_crit_demo.json",
    "TSP_crit": "lmetrics_TSP_crit28_example.json",
}

def load_metrics(path):
    with open(path) as f:
        d = json.load(f)

    return {
        "k": d.get("kappa_eff"),
        "H": d.get("entropy_eff"),
        "chi": d.get("chi_compactness"),
        "signature": (
            d.get("decision_class"),
            d.get("time_regime"),
            d.get("horizon_flag"),
        )
    }

def dist(a, b):
    return math.sqrt(
        (a["k"] - b["k"])**2 +
        (a["H"] - b["H"])**2 +
        (a["chi"] - b["chi"])**2
    )

def run():
    print("\n[Axis C — Representation Collapse Test]\n")

    data = {}
    for name, file in FILES.items():
        with open(file) as f:
            data[name] = load_metrics(file)

        print(f"{name:10s} → metrics = (k={data[name]['k']}, H={data[name]['H']}, χ={data[name]['chi']})")
        print(f"{'':10s}   signature = {data[name]['signature']}\n")

    print("[PAIRWISE DISTANCES]\n")

    for (a, b) in combinations(data.keys(), 2):
        d = dist(data[a], data[b])
        same_regime = data[a]["signature"] == data[b]["signature"]

        print(f"{a} ↔ {b}")
        print(f"  distance = {d:.4f}")
        print(f"  same regime = {same_regime}")

        if d < 0.1 and same_regime:
            print("  ⚠️  POSSIBILE COLLASSO")
        elif d < 0.1 and not same_regime:
            print("  ✔ separazione topologica confermata")
        else:
            print("  ✔ distanza sufficiente")

        print()

    print("[Axis C — Representation Collapse Test: COMPLETATO]\n")

if __name__ == "__main__":
    run()

