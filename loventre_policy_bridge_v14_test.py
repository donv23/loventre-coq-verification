
from loventre_lmetrics_core import mkMetrics
from loventre_policy_bridge_v14 import apply_policy_v14
from loventre_classes import classify

cases = [0,1,2,3,4]
print("=== Policy v14 Test ===")
for r in cases:
    m = mkMetrics(r)
    after = apply_policy_v14(m)
    print(
        f"risk={r:<2}",
        "→ class:", classify(m),
        "| policy→", classify(after),
        "| new_risk:", after.risk_level
    )

