"""
V13_NEXT / loventre_router_l8_v13.py
----------------------------------------
Layer 8 V13: Router di stack.

Prende un dizionario prodotto da ENTRYPOINT V13
e decide quale livello usare come "fonte ufficiale"
per la decisione finale del motore sandbox.

Regole:
  - WAIT → NON AGIRE (preferisci L7 action)
  - SAFE → usa L3 DECISION
  - SAFE_ACCESSIBLE → usa L4 BRIDGE
  - BLACKHOLE → segnala BL occulta e fallback su L3
"""

from V13_NEXT.L5_ENTRYPOINT.loventre_entrypoint_l5_v13 import run_entrypoint_v13
from V13_NEXT.L7_POLICY.loventre_policy_l7_v13 import compute_l7_policy_v13


def compute_l8_router_v13(raw_value=None):
    """
    Esegue ENTRYPOINT, quindi seleziona cosa pubblicare.
    """
    full = run_entrypoint_v13(raw_value)
    dec = full["decision_v13"]

    # L8 decisione di routing
    if dec == "WAIT":
        chosen_layer = "L7_POLICY"
        p = compute_l7_policy_v13(raw_value)
        result = {
            **full,
            **p,
            "selected_layer_v13": chosen_layer,
            "decision_published_v13": p["action_v13"],
        }

    elif dec == "SAFE":
        chosen_layer = "L3_DECISION"
        result = {
            **full,
            "selected_layer_v13": chosen_layer,
            "decision_published_v13": full["decision_v13"],
        }

    elif dec == "SAFE_ACCESSIBLE":
        chosen_layer = "L4_BRIDGE"
        result = {
            **full,
            "selected_layer_v13": chosen_layer,
            "decision_published_v13": full["bridge_decision_v13"],
        }

    elif dec == "BLACKHOLE":
        chosen_layer = "L3_DECISION"
        result = {
            **full,
            "selected_layer_v13": chosen_layer,
            "decision_published_v13": "BLACKHOLE_HARD_STOP",
            "note_v13": "Blackhole rilevato — fallback sicuro",
        }

    else:
        chosen_layer = "UNKNOWN"
        result = {
            **full,
            "selected_layer_v13": chosen_layer,
            "decision_published_v13": "UNDEFINED",
        }

    result["meta_label_v13"] = "L8_ROUTER_V13"
    return result


def demo():
    print("=== DEMO L8 ROUTER V13 ===")
    for raw in [None, -0.2, 0.2, 0.7, 1.2]:
        out = compute_l8_router_v13(raw)
        print(
            f"raw={str(raw):>5} "
            f"| dec_pub={out['decision_published_v13']:>20} "
            f"| selected={out['selected_layer_v13']:>12}"
        )


if __name__ == "__main__":
    demo()

