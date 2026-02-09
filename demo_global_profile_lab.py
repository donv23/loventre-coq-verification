"""
demo_global_profile_lab.py
Loventre Engine — Global Profile 2D (kappa, entropy)
Gennaio 2026 — V6 LAB

Obiettivo:
  - esplorare l'effetto combinato di kappa_eff e entropy_eff
  - capire se l'entropia sposta o influenza il collasso
  - raccolta per future mappe (v7/surface/tunneling)

NOTA:
  - NON modifica la decisione globale (snapshot a kappa)
  - entropy influenza inerzia e rischio via mass + policy
"""

from loventre_global_entrypoint import loventre_global_decide_with_policy


def sweep_profile():
    # valori "a griglia"
    kappa_values = [3.0, 2.0, 1.0, 0.6, 0.3, 0.1, 0.0, -0.1, -0.3, -0.6, -1.0, -2.0]
    entropy_values = [0.0, 1.0, 2.5, 5.0]

    print("\n===== LOVENTRE ENGINE — GLOBAL PROFILE 2D (kappa, entropy) =====\n")
    print(f"Grid: {len(kappa_values)} x {len(entropy_values)} = {len(kappa_values)*len(entropy_values)} punti\n")

    for entropy in entropy_values:
        print(f"---------------------------------------------")
        print(f" ENTROPY = {entropy}")
        print(f"---------------------------------------------")

        for kappa in kappa_values:
            out = loventre_global_decide_with_policy(kappa_eff=kappa, entropy_eff=entropy)
            gd = out["loventre_global"]["global_decision"]
            risk = out.get("risk_class")
            color = out["loventre_global"]["global_color"]
            idx = out.get("risk_index")

            print(f"kappa={kappa:5.1f}  ->  decision={gd:9s}  risk={risk:5s}  inertia={idx}")


    print("\n===== END GLOBAL PROFILE 2D =====\n")


if __name__ == "__main__":
    sweep_profile()

