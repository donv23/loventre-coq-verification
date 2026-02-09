#!/usr/bin/env python3
"""
demo_global_entrypoint.py

Loventre Engine – Entry point globale v6
Gennaio 2026 — analisi singolo colpo (no iterazioni).

Esegue combinazioni predefinite di:
  - kappa_eff
  - entropy_eff (opzionale)
  - mass_eff = 1.0
e stampa decisioni, rischio, colori e hint.

Questo demo:
  * usa meta_decide_instance_with_mass_global (policy bridge V6)
  * NON altera kappa seed
  * NON esegue tunnel, iterazioni o feedback loop
  * stampa motivazioni policy correttamente
"""

from typing import Optional, Dict, Any
from policy.loventre_meta_decision_engine import (
    meta_decide_instance_with_mass_global,
)


def run_single_case(kappa: Optional[float], entropy: Optional[float]) -> Dict[str, Any]:
    """
    Esegue una sola istanza del motore con seed di kappa ed entropy opzionali.
    mass_eff fisso a 1.0 (v6).
    """
    kwargs: Dict[str, Any] = {}
    if kappa is not None:
        kwargs["kappa_eff"] = float(kappa)
    if entropy is not None:
        kwargs["entropy_eff"] = float(entropy)

    kwargs["mass_eff"] = 1.0  # per v6 è costante

    return meta_decide_instance_with_mass_global(**kwargs)


def pretty_print(metrics: Dict[str, Any]) -> None:
    """
    Stampa essenziale leggibile:
      decisione globale, colore, rischio, kappa, entropy, inertia, policy.
    """
    gd = metrics.get("loventre_global", {})
    decision = gd.get("global_decision", "?")
    color = gd.get("global_color", "?")
    score = gd.get("global_score", "?")

    kappa = metrics.get("kappa_eff")
    entropy = metrics.get("entropy_eff")
    inertia = metrics.get("inertial_idx")
    risk = metrics.get("risk_class")

    # Questa è la chiave giusta in V6
    reason = metrics.get("policy_hints", {}).get("reason", "No policy text")

    print(f"  decision={decision:<10} color={color:<6} score={score:<3} "
          f"kappa={kappa!s:>4} entropy={entropy!s:>4} "
          f"inertia={inertia!s:<4} risk={risk:<5}")
    print(f"    policy: {reason}")


def main() -> None:
    print("\n===== LOVENTRE ENGINE — GLOBAL ENTRYPOINT V6 =====\n")

    kappas = [3.0, 1.0, 0.3, 0.0, -0.1, -0.6, -2.0]
    entropies = [None, 1.0, 4.0]

    total = 0
    for e in entropies:
        print("---------------------------------------------")
        print(f" ENTROPY = {e}")
        print("---------------------------------------------")
        for k in kappas:
            total += 1
            metrics = run_single_case(k, e)
            pretty_print(metrics)

    print(f"\n===== END GLOBAL ENTRYPOINT V6 — {total} casi analizzati =====\n")


if __name__ == "__main__":
    main()

