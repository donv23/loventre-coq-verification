"""
V13_NEXT / loventre_policy_l7_v13.py
----------------------------------------
Layer 7 V13: suggerisce una policy operativa basata
su decisione e bus consolidati dello stack precedente.

NON tocca il core.
Valida solo per V13 sandbox.
"""

from V13_NEXT.L3_DECISION.loventre_decision_l3_v13 import compute_l3_decision_v13


def compute_l7_policy_v13(raw_value=None):
    """
    Determina una policy semplice basata sulla decisione V13.
    """
    d = compute_l3_decision_v13(raw_value)
    decision = d["decision_v13"]

    if decision == "WAIT":
        action = "DO_NOTHING"
        note = "input undefined o non affidabile — attendo"
    elif decision == "SAFE":
        action = "STEADY"
        note = "regime stabile — mantenere"
    elif decision == "SAFE_ACCESSIBLE":
        action = "EXPLORE_MORE"
        note = "zona produttiva — esplorare il potenziale"
    else:
        # BLACKHOLE o qualunque altro
        action = "ABORT_OR_RESTART"
        note = "input critico — fermare o riavviare"

    return {
        **d,
        "policy_action_v13": action,
        "policy_note_v13": note,
        "meta_label_v13": "POLICY_L7_V13",
    }


def demo():
    print("=== DEMO L7 POLICY V13 ===")
    for raw in [None, -1.0, -0.2, 0.2, 0.7, 1.2]:
        out = compute_l7_policy_v13(raw)
        print(
            f"raw={str(raw):>5} "
            f"| dec={out['decision_v13']:>16} "
            f"| action={out['policy_action_v13']:>18} "
            f"| note={out['policy_note_v13']}"
        )


if __name__ == "__main__":
    demo()

