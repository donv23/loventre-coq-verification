"""
V13_NEXT / loventre_consistency_l9_v13.py
----------------------------------------
Layer 9 V13: Consistency + Health Check.

Prende l'output di L8 router e verifica:
  • il valore pubblicato è coerente con L3/L4/L7
  • rileva inconsistenze palesi
  • imposta flag di health globale

Regole di base:
  - Se RAW è None → stato incerto, health=CHECK
  - Se pubblicato = WAIT/DO_NOTHING → health=CHECK
  - Se pubblicato = SAFE o SAFE_ACCESSIBLE → health=OK
  - Se BLACKHOLE_HARD_STOP → health=ALERT
"""

from V13_NEXT.L8_ROUTER.loventre_router_l8_v13 import compute_l8_router_v13


def compute_l9_consistency_v13(raw_value=None):
    """
    Esegue L8, poi applica filtri di consistenza e salubrità.
    """
    l8 = compute_l8_router_v13(raw_value)
    pub = l8["decision_published_v13"]

    # 1) coerenza semplice: NONE / WAIT
    if raw_value is None or pub in ["WAIT", "DO_NOTHING"]:
        health = "CHECK"
        consistent = False

    # 2) se siamo in zona stabile
    elif pub in ["SAFE", "SAFE_ACCESSIBLE"]:
        health = "OK"
        consistent = True

    # 3) Blackhole scenario
    elif pub == "BLACKHOLE_HARD_STOP":
        health = "ALERT"
        consistent = True   # coerente, ma pericoloso

    # 4) default: non classificabile
    else:
        health = "CHECK"
        consistent = False

    return {
        **l8,
        "consistent_v13": consistent,
        "health_flag_v13": health,
        "meta_label_v13": "L9_CONSISTENCY_V13",
    }


def demo():
    print("=== DEMO L9 CONSISTENCY V13 ===")
    for raw in [None, -0.2, 0.2, 0.7, 1.2]:
        out = compute_l9_consistency_v13(raw)
        print(
            f"raw={str(raw):>5} "
            f"| pub={out['decision_published_v13']:>20} "
            f"| health={out['health_flag_v13']:>7} "
            f"| consistent={out['consistent_v13']}"
        )


if __name__ == "__main__":
    demo()

