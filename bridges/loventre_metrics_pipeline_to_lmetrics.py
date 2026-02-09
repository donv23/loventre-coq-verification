#!/usr/bin/env python3
"""
LOVENTRE ENGINE – Pipeline: metrics JSON -> (metrics+Policy) -> LMetrics JSON
=============================================================================

Scopo:
  Dato un file JSON che rappresenta un bus "metrics" prodotto dal motore
  (o scritto a mano), eseguire in un colpo solo:

    1. Applicare il Policy Bridge (safe/borderline/critical/invalid)
       e scrivere un JSON arricchito con:

          global_decision_label
          global_decision_score
          global_meta_explanation

    2. Proiettare il metrics arricchito in un JSON "LMetrics-like"
       allineato al record Coq LMetrics, con chiavi canoniche:

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
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Dict

import loventre_policy_bridge as lpb
from loventre_project_metrics_to_lmetrics import project_metrics_to_lmetrics


def _apply_policy_bridge(metrics: Dict[str, Any]) -> Dict[str, Any]:
    """
    Applica il Policy Bridge usando il modulo loventre_policy_bridge.

    Preferenza:
      - se esiste lpb.apply_policy_bridge_to_metrics, usa quello;
      - altrimenti, se esiste lpb.append_policy_bridge_to_metrics, usa quello.
    """
    if hasattr(lpb, "apply_policy_bridge_to_metrics"):
        return lpb.apply_policy_bridge_to_metrics(metrics)  # type: ignore[attr-defined]
    if hasattr(lpb, "append_policy_bridge_to_metrics"):
        return lpb.append_policy_bridge_to_metrics(metrics)  # type: ignore[attr-defined]

    available = [name for name in dir(lpb) if "policy" in name or "bridge" in name]
    raise RuntimeError(
        "Loventre Policy Bridge non espone né 'apply_policy_bridge_to_metrics' "
        "né 'append_policy_bridge_to_metrics'. "
        f"Nomi disponibili nel modulo: {available}"
    )


# ============================================================
# CANON API (FIX B′.1)
# ============================================================

def metrics_to_lmetrics(metrics: Dict[str, Any]) -> Dict[str, Any]:
    """
    API canonica: dato un metrics dict,
    applica il Policy Bridge e restituisce il dict LMetrics-like.

    Questa funzione NON introduce nuova logica.
    È un alias stabile per uso programmatico.
    """
    metrics_enriched = _apply_policy_bridge(metrics)
    return project_metrics_to_lmetrics(metrics_enriched)


# ============================================================
# CLI
# ============================================================

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
            "Pipeline Loventre: metrics JSON -> metrics+Policy -> LMetrics JSON."
        )
    )
    parser.add_argument(
        "--input",
        "-i",
        required=True,
        help="Percorso al file JSON di input (metrics).",
    )
    parser.add_argument(
        "--metrics-out",
        default=None,
        help=(
            "Percorso al file JSON di output per il metrics arricchito dal Policy "
            "Bridge. Se non specificato, usa '<input>_with_global.json'."
        ),
    )
    parser.add_argument(
        "--lmetrics-out",
        default=None,
        help=(
            "Percorso al file JSON di output per il LMetrics proiettato. "
            "Se non specificato, usa 'lmetrics_from_<metrics-out-basename>.json'."
        ),
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()

    input_path = Path(args.input)

    # Nome di default per il metrics arricchito
    if args.metrics_out is not None:
        metrics_out_path = Path(args.metrics_out)
    else:
        stem = input_path.stem
        suffix = input_path.suffix or ".json"
        metrics_out_path = input_path.with_name(f"{stem}_with_global{suffix}")

    # Nome di default per il LMetrics proiettato
    if args.lmetrics_out is not None:
        lmetrics_out_path = Path(args.lmetrics_out)
    else:
        lstem = metrics_out_path.stem
        lsuffix = metrics_out_path.suffix or ".json"
        lmetrics_out_path = metrics_out_path.with_name(
            f"lmetrics_from_{lstem}{lsuffix}"
        )

    print(f"[INFO] Input        metrics JSON : {input_path}")
    print(f"[INFO] Output metrics+Policy JSON : {metrics_out_path}")
    print(f"[INFO] Output LMetrics JSON      : {lmetrics_out_path}")

    # 1) Carica metrics di partenza
    metrics = load_json(input_path)

    # 2) Applica Policy Bridge
    metrics_enriched = _apply_policy_bridge(metrics)
    save_json(metrics_out_path, metrics_enriched)
    print("[OK] Metrics arricchito con Policy Bridge salvato.")

    # 3) Proietta in LMetrics-like
    lmetrics = project_metrics_to_lmetrics(metrics_enriched)
    save_json(lmetrics_out_path, lmetrics)
    print("[OK] LMetrics proiettato e salvato.")
    print("     Chiavi principali LMetrics:")
    for k in sorted(lmetrics.keys()):
        print(f"       - {k}")


if __name__ == "__main__":
    main()

