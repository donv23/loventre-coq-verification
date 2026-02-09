"""
V13_NEXT / loventre_bus_l2_v13.py
------------------------------------
Layer 2 V13: classifica L1 in categorie di transizione.

Strato intermedio della pipeline V13:
  • prende kappa_l1 da compute_l1_metrics_v13
  • restituisce bus_state:
       SAFE-ish
       P_ACC-ish
       BLACKHOLE-ish
       UNDEFINED-ish
"""

from V13_NEXT.L1_METRICS.loventre_metrics_l1_v13 import compute_l1_metrics_v13


def compute_l2_bus_v13(raw_value=None):
    """
    Determina una classe L2 a partire da kappa grezzo,
    passando sempre da L1 V13.
    """

    l1 = compute_l1_metrics_v13(raw_value)

    k = l1["kappa_l1"]

    if k is None:
        bus = "UNDEFINED-ish"
    elif k < 0.0:
        bus = "BLACKHOLE-ish"
    elif k < 0.8:
        bus = "SAFE-ish"
    else:
        bus = "P_ACC-ish"

    return {
        **l1,
        "bus_state_v13": bus,
        "meta_label_v13": "BUS_L2_V13",
    }


def demo():
    print("=== DEMO L2 BUS V13 ===")
    for raw in [None, -1.0, -0.3, 0.1, 0.6, 0.9, 2.0]:
        out = compute_l2_bus_v13(raw)
        print(f"raw={str(raw):>4} → kappa={str(out['kappa_l1']):>4} | bus={out['bus_state_v13']}")


if __name__ == "__main__":
    demo()

