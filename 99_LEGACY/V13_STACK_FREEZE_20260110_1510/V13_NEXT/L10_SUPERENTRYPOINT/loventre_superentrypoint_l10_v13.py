"""
V13_NEXT / loventre_superentrypoint_l10_v13.py
----------------------------------------------
Layer 10: SUPER ENTRYPOINT

È la porta pubblica della pipeline V13.
Chiama L9 (che richiama internamente tutto il resto)
e ritorna SOLO le informazioni essenziali.

Serve per:
  • offrire un'API stabile e minimale
  • nascondere i dettagli interni dei layer
  • ridurre il rischio di rotture verso l'esterno
"""

from V13_NEXT.L9_CONSISTENCY.loventre_consistency_l9_v13 import compute_l9_consistency_v13


def run_l10_superentrypoint_v13(raw_value=None):
    """
    Chiamata finale ufficiale V13:
      L1..L9 → L10 ridotto
    """
    full = compute_l9_consistency_v13(raw_value)

    # Scegliamo le chiavi pubbliche
    published = {
        "decision_v13": full["decision_published_v13"],
        "color_v13": full["bridge_color_v13"],
        "score_v13": full["bridge_score_v13"],
        "health_flag_v13": full["health_flag_v13"],
        "consistent_v13": full["consistent_v13"],
        "meta_label_v13": "SUPERENTRYPOINT_V13",
    }

    return published


def demo():
    print("=== DEMO SUPERENTRYPOINT V13 ===")
    for raw in [None, -1.0, -0.2, 0.2, 0.7, 1.2]:
        out = run_l10_superentrypoint_v13(raw)
        print(
            f"raw={str(raw):>5} "
            f"| dec={out['decision_v13']:>16} "
            f"| col={out['color_v13']:>6} "
            f"| score={out['score_v13']:.1f} "
            f"| health={out['health_flag_v13']:>6} "
            f"| consistent={out['consistent_v13']}"
        )


if __name__ == "__main__":
    demo()

