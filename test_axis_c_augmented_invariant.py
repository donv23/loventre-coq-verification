import json
import math

FILES = {
    "SAT_crit": "lmetrics_SAT_crit16_eps_+0.000.json",
    "3SAT_crit": "metrics_3SAT_crit_demo.json",
    "TSP_crit": "lmetrics_TSP_crit28_example.json",
}

def load_signature(path):
    with open(path) as f:
        d = json.load(f)

    return {
        "kappa": d.get("kappa_eff"),
        "entropy": d.get("entropy_eff"),
        "chi": d.get("chi_compactness"),
        "time": d.get("time_regime"),
        "horizon": d.get("horizon_flag"),
    }

def metric_distance(a, b):
    return math.sqrt(
        (a["kappa"] - b["kappa"])**2 +
        (a["entropy"] - b["entropy"])**2 +
        (a["chi"] - b["chi"])**2
    )

print("\n[Axis C — Augmented Structural Invariant Test]\n")

signatures = {}
for name, file in FILES.items():
    sig = load_signature(file)
    signatures[name] = sig
    print(f"{name:10s} → "
          f"(k={sig['kappa']}, H={sig['entropy']}, χ={sig['chi']}) | "
          f"time={sig['time']} horizon={sig['horizon']}")

print("\n[PAIRWISE CHECK]\n")

names = list(signatures.keys())
for i in range(len(names)):
    for j in range(i+1, len(names)):
        A, B = names[i], names[j]
        sA, sB = signatures[A], signatures[B]

        d = metric_distance(sA, sB)
        structural_equal = (
            sA["time"] == sB["time"] and
            sA["horizon"] == sB["horizon"]
        )

        print(f"{A} ↔ {B}")
        print(f"  metric distance = {round(d,4)}")
        print(f"  same structural signature = {structural_equal}")

        if d < 0.05 and structural_equal:
            print("  ⚠️  metrically close AND structurally equal → potential collapse")
        elif d < 0.05 and not structural_equal:
            print("  ✔ metrically close BUT structurally separated")
        else:
            print("  ✔ distance sufficient")
        print()

print("[Axis C — Augmented Structural Invariant Test: COMPLETATO]\n")

