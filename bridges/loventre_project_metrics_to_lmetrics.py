#!/usr/bin/env python3
"""
LOVENTRE ENGINE – Proiezione metrics -> LMetrics JSON
=====================================================

Scopo:
  - prendere un file JSON "metrics" prodotto dal motore / dalle demo
    (es. metrics_TSP_crit28_demo_with_global.json),
  - estrarre i campi rilevanti per il record Coq `LMetrics`,
  - mappare la decisione globale di Policy Bridge su costruttori Coq:

        "safe"       -> "GD_safe"
        "borderline" -> "GD_borderline"
        "critical"   -> "GD_critical"
        "invalid"    -> "GD_invalid"

  - produrre un nuovo JSON "LMetrics" con chiavi canoniche:

        kappa_eff, entropy_eff, V0, a_min,
        p_tunnel, P_success,
        gamma_dilation, time_regime,
        mass_eff, inertial_idx,
        risk_index, risk_class,
        meta_label,
        chi_compactness, horizon_flag,
        loventre_global_decision,
        loventre_global_color,
        loventre_global_score

Uso esempio:

  python3 loventre_project_metrics_to_lmetrics.py \
      --input metrics_TSP_crit28_demo_with_global.json

  -> lmetrics_from_metrics_TSP_crit28_demo_with_global.json
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Dict


def _safe_get(d: Dict[str, Any], key: str, default: Any = None) -> Any:
    """Accesso robusto a d[key] con default."""
    if not isinstance(d, dict):
        return default
    return d.get(key, default)


def _map_global_label_to_coq(label: Any) -> str:
    """
    Mappa la stringa globale Python ("safe" | "borderline" | "critical" | "invalid")
    al costruttore Coq GlobalDecision ("GD_safe" | ...).
    """
    s = str(label or "").strip().lower()
    if s == "safe":
        return "GD_safe"
    if s == "borderline":
        return "GD_borderline"
    if s == "critical":
        return "GD_critical"
    if s == "invalid":
        return "GD_invalid"
    # fallback prudenziale
    return "GD_invalid"


def _map_global_color_to_coq(color: Any) -> str:
    """
    Mappa il colore operativo ("GREEN" | "AMBER" | "RED") al costruttore Coq GlobalColor.
    """
    s = str(color or "").strip().upper()
    if s == "GREEN":
        return "GC_green"
    if s == "AMBER":
        return "GC_amber"
    if s == "RED":
        return "GC_red"
    # fallback neutro
    return "GC_unknown"


def project_metrics_to_lmetrics(metrics: Dict[str, Any]) -> Dict[str, Any]:
    """
    Proietta un dict "metrics" generico del motore in un dict "LMetrics-like"
    con chiavi canoniche per Coq.
    """
    # Blocco operativo loventre_global, se esiste
    lg = _safe_get(metrics, "loventre_global", {})
    if not isinstance(lg, dict):
        lg = {}

    # Policy Bridge (global_decision_label / score)
    pb_label = _safe_get(metrics, "global_decision_label", None)
    pb_score = _safe_get(metrics, "global_decision_score", None)

    # Scegliamo la sorgente per la decisione globale Coq-level:
    # - se c'è la label di Policy Bridge, usiamo quella;
    # - altrimenti inferiamo da loventre_global.global_decision (INSISTI/VALUTA/RITIRA)
    #   ma questo è più grezzo, quindi preferiamo il primo caso.
    if pb_label is not None:
        coq_dec = _map_global_label_to_coq(pb_label)
        dec_score = pb_score
    else:
        # fallback: mappiamo INSISTI/VALUTA/RITIRA in safe/borderline/critical
        op_dec = str(_safe_get(lg, "global_decision", "UNKNOWN") or "").upper()
        if op_dec == "INSISTI":
            coq_dec = "GD_safe"
        elif op_dec == "VALUTA":
            coq_dec = "GD_borderline"
        elif op_dec == "RITIRA":
            coq_dec = "GD_critical"
        else:
            coq_dec = "GD_invalid"
        dec_score = _safe_get(lg, "global_score", None)

    coq_color = _map_global_color_to_coq(_safe_get(lg, "global_color", None))

    # Costruiamo il dict LMetrics-like
    lmetrics: Dict[str, Any] = {
        # Geometric / energetic
        "kappa_eff": _safe_get(metrics, "kappa_eff", None),
        "entropy_eff": _safe_get(metrics, "entropy_eff", None),
        "V0": _safe_get(metrics, "V0", None),
        "a_min": _safe_get(metrics, "a_min", None),

        # Tunneling & success probability
        "p_tunnel": _safe_get(metrics, "p_tunnel", None),
        "P_success": _safe_get(metrics, "P_success", None),

        # Relativistic / mass-like indices
        "gamma_dilation": (
            _safe_get(metrics, "gamma_dilation",
                      _safe_get(metrics, "gamma_schw", None))
        ),
        "time_regime": _safe_get(metrics, "time_regime", "unknown"),
        "mass_eff": _safe_get(metrics, "mass_eff", None),
        "inertial_idx": _safe_get(metrics, "inertial_idx", None),

        # Risk & meta
        "risk_index": _safe_get(metrics, "risk_index", None),
        "risk_class": _safe_get(metrics, "risk_class", "UNKNOWN"),
        "meta_label": _safe_get(metrics, "meta_label", "unknown"),

        # Compactness / horizon
        "chi_compactness": _safe_get(metrics, "chi_compactness", None),
        "horizon_flag": _safe_get(metrics, "horizon_flag", False),

        # Global decision (Coq-level)
        "loventre_global_decision": coq_dec,
        "loventre_global_color": coq_color,
        "loventre_global_score": dec_score,
    }

    return lmetrics


def load_json(path: Path) -> Dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"File non trovato: {path}")
    with path.open("r", encoding="utf-8") as f:
        data = json.load(f)
    if not isinstance(data, dict):
        raise ValueError("Il JSON non contiene un oggetto/dict alla radice.")
    return data


def save_json(path: Path, obj: Dict[str, Any]) -> None:
    with path.open("w", encoding="utf-8") as f:
        json.dump(obj, f, indent=2, sort_keys=True, ensure_ascii=False)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Proietta un file metrics JSON in un JSON LMetrics-like "
            "allineato al record Coq LMetrics."
        )
    )
    parser.add_argument(
        "--input",
        "-i",
        required=True,
        help="Percorso al file JSON di input (metrics).",
    )
    parser.add_argument(
        "--output",
        "-o",
        default=None,
        help=(
            "Percorso al file JSON di output. "
            "Se non specificato, usa 'lmetrics_from_<input_basename>.json'."
        ),
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()

    input_path = Path(args.input)
    if args.output is not None:
        output_path = Path(args.output)
    else:
        stem = input_path.stem
        suffix = input_path.suffix or ".json"
        output_path = input_path.with_name(f"lmetrics_from_{stem}{suffix}")

    print(f"[INFO] Input  metrics JSON : {input_path}")
    print(f"[INFO] Output LMetrics JSON: {output_path}")

    metrics = load_json(input_path)
    lmetrics = project_metrics_to_lmetrics(metrics)
    save_json(output_path, lmetrics)

    print("[OK] Proiezione completata.")
    print("     Chiavi principali LMetrics:")
    for k in sorted(lmetrics.keys()):
        print(f"       - {k}")


if __name__ == "__main__":
    main()

