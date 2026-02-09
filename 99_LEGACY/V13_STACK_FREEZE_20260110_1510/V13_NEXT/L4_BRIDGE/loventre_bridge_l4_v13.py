"""
V13_NEXT / loventre_bridge_l4_v13.py
----------------------------------------
Layer 4 V13: bridge locale (no CORE).
Traduce la decisione L3 in:
  • colore
  • punteggio
  • decisione 'bridge'
"""

from V13_NEXT.L3_DECISION.loventre_decision_l3_v13 import compute_l3_decision_v13


def compute_l4_bridge_v13(raw_value=None):
    """
    Traduce decision_v13 in attributi visual/score
    senza dipendenze dal CORE.
    """

    dec = compute_l3_decision_v13(raw_value)
    decision = dec["decision_v13"]

    # Mapping dei colori
    if decision == "SAFE_ACCESSIBLE":
        color = "BLUE"
        score = 1.0
    elif decision == "SAFE":
        color = "GREEN"
        score = 0.8
    elif decision == "BLACKHOLE":
        color = "RED"
        score = 0.0
    else:  # WAIT
        color = "YELLOW"
        score = 0.5

    return {
        **dec,
        "bridge_decision_v13": decision,
        "bridge_color_v13": color,
        "bridge_score_v13": score,
        "meta_label_v13": "L4_BRIDGE_V13",
    }


def demo():
    print("=== DEMO L4 BRIDGE V13 ===")
    for raw in [None, -1.0, -0.2, 0.2, 0.7, 1.2]:
        out = compute_l4_bridge_v13(raw)
        print(
            f"raw={str(raw):>5} "
            f"| kappa={str(out['kappa_l1']):>4} "
            f"| dec={out['decision_v13']:>16} "
            f"| color={out['bridge_color_v13']:>6} "
            f"| score={out['bridge_score_v13']:.1f}"
        )


if __name__ == "__main__":
    demo()

