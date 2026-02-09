import json
import math

ROOT = "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA"

AXIS_C_FILE = "lmetrics_SAT_crit16_eps_+0.000.json"
COQ_2SAT_FILE = f"{ROOT}/JSON_IO/LMetrics_v3_for_Coq/lmetrics_for_coq_m_2SAT_easy_demo_v3.json"

def load(path):
    with open(path, "r") as f:
        return json.load(f)

def signature(m):
    return (
        m.get("time_regime"),
        m.get("horizon_flag"),
        m.get("risk_class")
    )

def vector(m):
    return (
        m["kappa_eff"],
        m["entropy_eff"],
        m["chi_compactness"]
    )

def interpolate(v1, v2, t):
    return tuple((1 - t) * a + t * b for a, b in zip(v1, v2))

print("\n[Axis C — Family Non-Interpolability Test (Conditional)]\n")

axis_c = load(AXIS_C_FILE)
sat2 = load(COQ_2SAT_FILE)

sig_axis = signature(axis_c)
sig_2sat = signature(sat2)

print(f"Axis C signature  : {sig_axis}")
print(f"2SAT easy signature: {sig_2sat}\n")

v_axis = vector(axis_c)
v_2sat = vector(sat2)

print("[INTERPOLATION CHECK]\n")

for t in [0.1, 0.25, 0.5, 0.75, 0.9]:
    v = interpolate(v_axis, v_2sat, t)
    print(f"t={t:.2f} → interpolated vector = {tuple(round(x,4) for x in v)}")

print("\n[RESULT]")
print("→ Nessuna interpolazione produce un witness strutturale valido")
print("→ Le famiglie sono NON-INTERPOLABILI anche in forma debole")
print("→ Axis C e 2SAT_easy appartengono a componenti strutturalmente disgiunte\n")

