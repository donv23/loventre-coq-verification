"""
loventre_tunneling_v15_test.py — test del tunneling
"""
from random import seed
from loventre_lmetrics_core import mkMetrics
from loventre_risk_class import classify
from loventre_tunneling_v15 import tunneling_step

seed(99)

print("=== TUNNELING v15 ===")
for r in range(0,6):
    m = mkMetrics(r)
    m2 = tunneling_step(m)
    print(
        f"risk={r:1} → class:{classify(m):14} | tunnel→ {m2}"
    )

