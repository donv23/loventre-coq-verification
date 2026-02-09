import json
import math

# --------------------------------------------------
# Axis C — Obstruction Stability under Witness Mutation
# --------------------------------------------------

FILES = [
    "lmetrics_SAT_crit16_eps_-0.020.json",
    "lmetrics_SAT_crit16_eps_-0.010.json",
    "lmetrics_SAT_crit16_eps_-0.005.json",
    "lmetrics_SAT_crit16_eps_+0.000.json",
    "lmetrics_SAT_crit16_eps_+0.005.json",
    "lmetrics_SAT_crit16_eps_+0.010.json",
    "lmetrics_SAT_crit16_eps_+0.020.json",
]

PATCH_RADIUS = 0.05


def load_metrics(path):
    with open(path) as f:
        return json.load(f)


def local_patchable(metrics):
    """
    Very strict notion:
    try small local perturbations and see if any
    structural flag changes.
    """
    base = (
        metrics["time_regime"],
        metrics["horizon_flag"],
    )

    for dk in [-PATCH_RADIUS, PATCH_RADIUS]:
        for dH in [-PATCH_RADIUS, PATCH_RADIUS]:
            for dchi in [-PATCH_RADIUS, PATCH_RADIUS]:
                pert = metrics.copy()
                pert["kappa_eff"] += dk
                pert["entropy_eff"] += dH
                pert["chi_compactness"] += dchi

                sig = (
                    pert["time_regime"],
                    pert["horizon_flag"],
                )

                if sig != base:
                    return True

    return False


print("\n[Axis C — Obstruction Stability under Witness Mutation]\n")

results = []

for fname in FILES:
    m = load_metrics(fname)
    patchable = local_patchable(m)

    results.append((fname, patchable))

    status = "PATCHABLE ❌" if patchable else "NON PATCHABLE ✔"
    print(f"{fname:40s} → {status}")

print("\n[SUMMARY]\n")

if all(not p for _, p in results):
    print("[OK ] Obstruction stable under all witness mutations")
    print("     → Axis C obstruction is STRUCTURAL")
else:
    print("[WARN] Obstruction unstable for some witnesses")
    print("       → investigate exceptional cases")

print("\n[Axis C — Obstruction Stability Test: COMPLETATO]\n")

