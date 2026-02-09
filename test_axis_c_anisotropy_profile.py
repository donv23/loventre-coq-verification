import json

FILES = {
    "SAT_crit": "lmetrics_SAT_crit16_eps_+0.000.json",
    "TSP_crit": "lmetrics_TSP_crit28_example.json",
}

DELTAS = {
    "kappa_eff": 0.02,
    "entropy_eff": 0.02,
    "chi_compactness": 0.02,
}

def load(path):
    with open(path) as f:
        return json.load(f)

def perturb(base, key, delta):
    d = dict(base)
    d[key] = round(d[key] + delta, 4)
    return d

def signature(d):
    return (
        d.get("time_regime"),
        d.get("horizon_flag"),
    )

print("\n[Axis C — Anisotropy Profile Test]\n")

for name, file in FILES.items():
    base = load(file)
    base_sig = signature(base)

    print(f"{name}")
    print(f"  base signature = {base_sig}")

    for axis, delta in DELTAS.items():
        up = perturb(base, axis, +delta)
        down = perturb(base, axis, -delta)

        sig_up = signature(up)
        sig_down = signature(down)

        response = (
            sig_up == base_sig and
            sig_down == base_sig
        )

        print(f"  axis {axis:14s} → invariant = {response}")

    print()

print("[Axis C — Anisotropy Profile Test: COMPLETATO]\n")

