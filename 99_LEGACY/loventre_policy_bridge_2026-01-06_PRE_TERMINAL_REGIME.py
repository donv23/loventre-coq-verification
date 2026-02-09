"""
loventre_policy_bridge.py
Policy Bridge – Recovery conservativo (A2)
Gennaio 2026

Principi:
- NON modifica la decisione globale
- NON modifica score o colore
- NON introduce logica causale
- Annotazione puramente descrittiva
"""

from typing import Any, Dict


def apply_policy_bridge_to_metrics(metrics: Dict[str, Any]) -> Dict[str, Any]:
    """
    Policy bridge conservativo.

    - Preserva integralmente la decisione snapshot
    - Aggiunge solo suggerimenti descrittivi (policy_hints)
    - Attiva prudenza se viene rilevata isteresi sotto BLACKHOLE
    """
    m = dict(metrics)

    # --- Preserva campi decisionali ---
    m.setdefault("global_decision_label", "GD_safe")
    m.setdefault("global_decision_score", 1.0)

    # --- Lettura segnali osservativi ---
    decision = (
        m.get("loventre_global", {}) or {}
    ).get("global_decision")

    hysteresis = bool(m.get("hysteresis_detected", False))

    # --- Policy hints (descrittivi, non attivi) ---
    policy_hints = {
        "recovery_advised": False,
        "monitoring_recommended": False,
        "reason": "No special condition detected"
    }

    if decision == "BLACKHOLE" and hysteresis:
        policy_hints = {
            "recovery_advised": False,
            "monitoring_recommended": True,
            "reason": "Hysteresis detected under snapshot blackhole"
        }

    m["policy_hints"] = policy_hints

    # --- Spiegazione globale (descrittiva) ---
    m["global_meta_explanation"] = (
        "Conservative policy bridge applied. "
        "Decision snapshot preserved; observability annotated."
    )

    return m

