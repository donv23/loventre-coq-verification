"""
run_v13_suite.py
------------------------------------
Mini suite automatica per V13: L1→L10
"""

import sys
import traceback

TESTS = []


def register(name, func):
    TESTS.append((name, func))


# ===== IMPORT =====
from V13_NEXT.L1_METRICS.loventre_metrics_l1_v13 import compute_l1_metrics_v13
from V13_NEXT.L2_BUS.loventre_bus_l2_v13 import compute_l2_bus_v13
from V13_NEXT.L3_DECISION.loventre_decision_l3_v13 import compute_l3_decision_v13
from V13_NEXT.L4_BRIDGE.loventre_bridge_l4_v13 import compute_l4_bridge_v13
from V13_NEXT.L5_ENTRYPOINT.loventre_entrypoint_l5_v13 import run_entrypoint_v13
from V13_NEXT.L6_EXPORT.loventre_export_l6_v13 import run_export_l6_v13
from V13_NEXT.L7_POLICY.loventre_policy_l7_v13 import compute_l7_policy_v13
from V13_NEXT.L8_ROUTER.loventre_router_l8_v13 import compute_l8_router_v13
from V13_NEXT.L9_CONSISTENCY.loventre_consistency_l9_v13 import compute_l9_consistency_v13
from V13_NEXT.L10_SUPERENTRYPOINT.loventre_superentrypoint_l10_v13 import (
    run_l10_superentrypoint_v13,
)


# ===== Test definitions =====
register("L1 metrics", lambda: compute_l1_metrics_v13(0.3))
register("L2 bus", lambda: compute_l2_bus_v13(0.3))
register("L3 decision", lambda: compute_l3_decision_v13(0.3))
register("L4 bridge", lambda: compute_l4_bridge_v13(0.3))
register("L5 entrypoint", lambda: run_entrypoint_v13(0.3))
register("L6 export", lambda: run_export_l6_v13())
register("L7 policy", lambda: compute_l7_policy_v13(0.3))
register("L8 router", lambda: compute_l8_router_v13(0.3))
register("L9 consistency", lambda: compute_l9_consistency_v13(0.3))
register("L10 superentrypoint", lambda: run_l10_superentrypoint_v13(0.3))


# ===== RUN SUITE =====
print("\n===== V13 MINI SUITE =====\n")

success = 0
fail = 0

for name, fn in TESTS:
    try:
        print(f"[RUN ] {name}")
        fn()
        print(f"[ OK ] {name}\n")
        success += 1
    except Exception as e:
        fail += 1
        print(f"[ERR] {name} → {e}")
        traceback.print_exc()
        print("")

print("===== RISULTATI V13 =====")
print(f"SUCCESSI : {success}")
print(f"FALLIMENTI : {fail}")
status = "✔ ALL GREEN (Sandbox V13 pulita)" if fail == 0 else "⚠ CHECK NEEDED"
print(f"STATO : {status}")
print("\n===== END V13 MINI SUITE =====")

