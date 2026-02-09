import json
from pathlib import Path

# ===============================
# Axis C — Witness Replacement Obstruction Test
# ===============================

BASE_WITNESS = "lmetrics_SAT_crit16_eps_+0.000.json"

OTHER_WITNESSES = [
    "metrics_2SAT_crit_demo.json",
    "metrics_3SAT_crit_demo.json",
    "lmetrics_TSP_crit28_example.json",
]

ROOT = Path(".")
FILES = [BASE_WITNESS] + OTHER_WITNESSES

def load_signature(fname):
    with open(ROOT / fname) as f:
        data = json.load(f)
    return {
        "file": fname,
        "kappa": round(data.get("kappa_eff", 0), 3),
        "entropy": round(data.get("entropy_eff", 0), 3),
        "chi": round(data.get("chi_compactness", 0), 3),
        "horizon": data.get("horizon_flag"),
        "time": data.get("time_regime"),
        "decision": data.get("decision_class"),
    }

print("\n[Axis C — Witness Replacement Obstruction Test]\n")

signatures = []
for f in FILES:
    if not (ROOT / f).exists():
        print(f"[SKIP] missing file: {f}")
        continue
    signatures.append(load_signature(f))

# stampa tabella comparativa
for s in signatures:
    print(
        f"{s['file']:<40} | "
        f"k={s['kappa']:<5} "
        f"H={s['entropy']:<5} "
        f"χ={s['chi']:<5} | "
        f"time={s['time']:<15} "
        f"horizon={s['horizon']} "
        f"decision={s['decision']}"
    )

# verifica strutturale
base = signatures[0]
print("\n[STRUCTURAL CHECK]\n")

for s in signatures[1:]:
    same_decision = s["decision"] == base["decision"]
    same_time = s["time"] == base["time"]
    same_horizon = s["horizon"] == base["horizon"]

    if same_decision and same_time and same_horizon:
        print(f"[FAIL] {s['file']} → nessun salto strutturale rilevato")
    else:
        print(f"[OK ] {s['file']} → witness replacement necessario")

print("\n[Axis C — Witness Replacement Obstruction: COMPLETATO]\n")

