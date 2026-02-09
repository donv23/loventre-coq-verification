"""
V13_NEXT / loventre_entrypoint_l5_v13.py
------------------------------------------------
Entry point V13 minimale:
    L1 → L2 → L3 → L4
Restituisce un unico snapshot consolidato.
Nessun CORE esterno per ora.
"""

from V13_NEXT.L1_METRICS.loventre_metrics_l1_v13 import compute_l1_metrics_v13
from V13_NEXT.L2_BUS.loventre_bus_l2_v13 import compute_l2_bus_v13
from V13_NEXT.L3_DECISION.loventre_decision_l3_v13 import compute_l3_decision_v13
from V13_NEXT.L4_BRIDGE.loventre_bridge_l4_v13 import compute_l4_bridge_v13


def run_entrypoint_v13(raw_value=None):
    """
    Chiamata unica V13 completa.
    Restituisce tutti gli strati L1-L2-L3-L4
    in un singolo dizionario coerente.
    """

    # Facciamo correre direttamente L4 (che incapsula L3-L2-L1),
    # ma includiamo anche i livelli intermedi in output.
    l1 = compute_l1_metrics_v13(raw_value)
    l2 = compute_l2_bus_v13(raw_value)
    l3 = compute_l3_decision_v13(raw_value)
    l4 = compute_l4_bridge_v13(raw_value)

    merged = {
        **l1,
        **l2,
        **l3,
        **l4,
        "meta_label_v13": "ENTRYPOINT_V13",
    }

    return merged


def demo():
    print("=== DEMO ENTRYPOINT V13 (FULL STACK L1–L4) ===")
    for raw in [None, -1.0, -0.2, 0.2, 0.7, 1.2]:
        out = run_entrypoint_v13(raw)
        print(
            f"raw={str(raw):>5} "
            f"| dec={out['decision_v13']:>16} "
            f"| bridge={out['bridge_decision_v13']:>16} "
            f"| color={out['bridge_color_v13']:>6} "
            f"| score={out['bridge_score_v13']:.1f}"
        )


if __name__ == "__main__":
    demo()

