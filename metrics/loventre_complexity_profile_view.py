#!/usr/bin/env python3
# loventre_complexity_profile_view.py
#
# Dicembre 2025 – Vista operativa dei profili di complessità
# P_like_complexity_profile / NP_like_crit_complexity_profile
# sui metrics_*.json, allineata a Loventre_LMetrics_Complexity_Profiles.v.
#
# Non modifica nulla, stampa solo una tabella riassuntiva.

import json
import os
from typing import Dict, Any, List, Tuple

# Lista dei file di metrics che vogliamo ispezionare.
METRICS_FILES: List[str] = [
    "metrics_SAT_crit16_demo.json",
    "metrics_SAT_crit16_demo_with_global.json",
    "metrics_TSP_crit28_demo.json",
    "metrics_TSP_crit28_demo_with_global.json",
    "metrics_seed11_cli_demo.json",
    "metrics_seed_grid_demo_global.json",
]


def load_metrics(path: str) -> Dict[str, Any]:
    """Carica un file JSON di metriche. Se manca o è rotto, alza un'eccezione."""
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def is_low_risk(m: Dict[str, Any]) -> bool:
    """
    Profilo low risk: accetta sia "LOW" sia "risk_LOW".
    """
    rc = m.get("risk_class")
    return rc in ("LOW", "risk_LOW")


def is_black_hole(m: Dict[str, Any]) -> bool:
    return m.get("horizon_flag") is True


def is_non_black_hole(m: Dict[str, Any]) -> bool:
    return m.get("horizon_flag") is False


def is_NP_like_black_hole_risk(m: Dict[str, Any]) -> bool:
    """
    Profilo NP-like black-hole: accetta sia "NP_like_black_hole"
    sia "risk_NP_like_black_hole".
    """
    rc = m.get("risk_class")
    return rc in ("NP_like_black_hole", "risk_NP_like_black_hole")


def P_like_complexity_profile(m: Dict[str, Any]) -> bool:
    """
    Versione Python del profilo P_like_complexity_profile:
      is_low_risk(m) and is_non_black_hole(m).
    """
    return is_low_risk(m) and is_non_black_hole(m)


def NP_like_crit_complexity_profile(m: Dict[str, Any]) -> bool:
    """
    Versione Python del profilo NP_like_crit_complexity_profile:
      is_NP_like_black_hole_risk(m) and is_black_hole(m).
    """
    return is_NP_like_black_hole_risk(m) and is_black_hole(m)


def classify_complexity_profile(m: Dict[str, Any]) -> str:
    """
    Ritorna un'etichetta testuale:
      - "P_like_complexity"
      - "NP_like_crit_complexity"
      - "OTHER"
      - oppure "INCONSISTENT(P_and_NPcrit)" se capitasse qualcosa di paradossale.
    """
    is_P = P_like_complexity_profile(m)
    is_NPcrit = NP_like_crit_complexity_profile(m)

    if is_P and is_NPcrit:
        # In teoria impossibile se risk_class e horizon_flag sono coerenti,
        # ma la segnaliamo nel caso di JSON corrotti.
        return "INCONSISTENT(P_and_NPcrit)"

    if is_P:
        return "P_like_complexity"
    if is_NPcrit:
        return "NP_like_crit_complexity"
    return "OTHER"


def get_basic_info(m: Dict[str, Any]) -> Tuple[str, str, bool, str, str]:
    """
    Estrae qualche campo chiave per riassumere la riga:
      - meta_label
      - risk_class
      - horizon_flag
      - loventre_global_decision
      - loventre_global_color
    (se mancano o sono null, usa placeholder).
    """

    def norm(x: Any) -> str:
        return "<?>" if x is None else str(x)

    meta_label = norm(m.get("meta_label"))
    risk = norm(m.get("risk_class"))
    horizon = bool(m.get("horizon_flag", False))
    decision = norm(m.get("loventre_global_decision"))
    color = norm(m.get("loventre_global_color"))
    return meta_label, risk, horizon, decision, color


def main() -> None:
    print("Loventre Complexity Profile View")
    print("================================\n")

    root = os.getcwd()
    rows: List[Tuple[str, str, str, str, str, str, str]] = []

    for fname in METRICS_FILES:
        path = os.path.join(root, fname)
        if not os.path.exists(path):
            rows.append((fname, "MISSING", "-", "-", "-", "-", "-"))
            continue

        try:
            m = load_metrics(path)
        except Exception as e:
            rows.append((fname, f"ERROR({e})", "-", "-", "-", "-", "-"))
            continue

        profile = classify_complexity_profile(m)
        meta_label, risk, horizon, decision, color = get_basic_info(m)

        rows.append((
            fname,
            profile,
            meta_label,
            risk,
            "true" if horizon else "false",
            decision,
            color,
        ))

    # Stampa una tabella semplice in stile markdown.
    header = [
        "file",
        "complexity_profile",
        "meta_label",
        "risk_class",
        "horizon_flag",
        "decision",
        "color",
    ]

    print("| " + " | ".join(header) + " |")
    print("| " + " | ".join(["---"] * len(header)) + " |")
    for row in rows:
        print("| " + " | ".join(row) + " |")

    print("\nNota:")
    print("- P_like_complexity  := (risk_class ∈ {LOW, risk_LOW})  ∧ (horizon_flag = false)")
    print("- NP_like_crit_complexity := (risk_class ∈ {NP_like_black_hole, risk_NP_like_black_hole}) ∧ (horizon_flag = true)")
    print("Questi profili sono la controparte JSON di Loventre_LMetrics_Complexity_Profiles.v.")


if __name__ == "__main__":
    main()

