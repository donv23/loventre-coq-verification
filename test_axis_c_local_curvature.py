import json
import copy

# =========================
# CONFIG
# =========================
BASE_FILE = "lmetrics_SAT_crit16_eps_+0.000.json"
DELTA = 0.02

AXES = {
    "KAPPA": "kappa_eff",
    "ENTROPY": "entropy_eff",
    "CHI": "chi_compactness"
}

# =========================
# LOAD BASE
# =========================
with open(BASE_FILE) as f:
    base = json.load(f)

def potential(m):
    """
    Potenziale Loventre minimale.
    Non inventiamo nulla: usiamo una combinazione stabile
    coerente con i test precedenti.
    """
    return (
        m["kappa_eff"]
        + m["entropy_eff"]
        + m["chi_compactness"]
    )

V0 = potential(base)

results = []

# =========================
# CURVATURE TEST
# =========================
for axis, key in AXES.items():
    plus = copy.deepcopy(base)
    minus = copy.deepcopy(base)

    plus[key] += DELTA
    minus[key] -= DELTA

    V_plus = potential(plus)
    V_minus = potential(minus)

    curvature = V_plus - 2 * V0 + V_minus

    results.append({
        "axis": axis,
        "delta": DELTA,
        "V_minus": round(V_minus, 6),
        "V_0": round(V0, 6),
        "V_plus": round(V_plus, 6),
        "second_order_curvature": round(curvature, 8)
    })

# =========================
# OUTPUT
# =========================
print("\n[Axis C — Local Curvature Test]\n")
for r in results:
    print(r)

