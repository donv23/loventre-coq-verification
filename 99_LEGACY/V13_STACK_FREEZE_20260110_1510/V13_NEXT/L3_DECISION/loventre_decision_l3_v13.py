"""
V13_NEXT / loventre_decision_l3_v13.py
----------------------------------------
Layer 3 V13: decisione finale locale.

Input:
  • raw_value grezzo

Pipeline:
  L1 → L2 → decision

Decisioni finali:
  - SAFE
  - SAFE_ACCESSIBLE
  - BLACKHOLE
  - WAIT
"""

from V13_NEXT.L2_BUS.loventre_bus_l2_v13 import compute_l2_bus_v13


def compute_l3_decision_v13(raw_value=None):
    """
    Converte lo stato del bus L2 in una decisione high-level.
    """

    bus = compute_l2_bus_v13(raw_value)
    state = bus["bus_state_v13"]

    if state == "BLACKHOLE-ish":
        decision = "BLACKHOLE"
    elif state == "P_ACC-ish":
        decision = "SAFE_ACCESSIBLE"
    elif state == "SAFE-ish":
        decision = "SAFE"
    else:
        decision = "WAIT"

    return {
        **bus,
        "decision_v13": decision,
        "meta_label_v13": "L3_DECISION_V13",
    }


def demo():
    print("=== DEMO L3 DECISION V13 ===")
    for raw in [None, -1.0, -0.2, 0.2, 0.7, 1.2]:
        out = compute_l3_decision_v13(raw)
        print(f"raw={str(raw):>5} → kappa={str(out['kappa_l1']):>4} | bus={out['bus_state_v13']:>12} | dec={out['decision_v13']}")
        

if __name__ == "__main__":
    demo()

