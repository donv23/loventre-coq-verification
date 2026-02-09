"""
test_decision_comparison_CANON.py
Confronto decisione storica vs canonica
FASE 2.2 — dicembre 2025
"""

from loventre_meta_engine import loventre_collect_base_metrics, compute_barrier_diagnostic_v4
from loventre_decision_canon import decision_of_metrics

SEEDS = [
    {"param": 1, "factor": 1},
    {"param": 1, "factor": 2},
    {"param": 1, "factor": 3},
    {"param": 2, "factor": 2},
    {"param": 3, "factor": 3},
]

print("\n==============================")
print(" CONFRONTO DECISIONI LOVENTRE ")
print("==============================\n")

for seed in SEEDS:
    print("SEED:", seed)

    metrics = loventre_collect_base_metrics(seed)

    decision_engine = compute_barrier_diagnostic_v4(metrics)
    decision_canon = decision_of_metrics(metrics)

    print("  metrics:", {
        "kappa_eff": metrics.get("kappa_eff"),
        "entropy_eff": metrics.get("entropy_eff"),
        "V0": metrics.get("V0")
    })

    print("  decision_engine :", decision_engine)
    print("  decision_canon  :", decision_canon)

    if decision_engine != decision_canon:
        print("  ⚠️  DIVERGENZA")
    else:
        print("  ✔️  COERENZA")

    print("-" * 60)

print("\nFINE CONFRONTO\n")

