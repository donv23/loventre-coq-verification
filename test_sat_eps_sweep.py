import json
import copy

BASE = "lmetrics_SAT_crit16_example.json"
EPS = [-0.02, -0.01, -0.005, 0.0, 0.005, 0.01, 0.02]

with open(BASE) as f:
    base = json.load(f)

print("[Loventre][EPS-SWEEP] Avvio test SAT ε-sweep")

for eps in EPS:
    m = copy.deepcopy(base)
    m["entropy_eff"] = max(0.0, min(1.0, m["entropy_eff"] + eps))
    m["kappa_eff"] = max(0.0, min(1.0, m["kappa_eff"] + eps))
    m["gamma_dilation"] = m["gamma_dilation"] * (1.0 + eps)
    m["mass_eff"] = m["mass_eff"] * (1.0 + eps)

    fname = f"lmetrics_SAT_crit16_eps_{eps:+.3f}.json"
    with open(fname, "w") as g:
        json.dump(m, g, indent=2)

    print(f"[OK] scritto {fname}")

print("[Loventre][EPS-SWEEP] File generati")

