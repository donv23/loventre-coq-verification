#!/usr/bin/env python3
"""
LOVENTRE ENGINE – loventre_metrics_enrich_with_policy_bridge.py
===============================================================

Scopo:
  - leggere un file JSON contenente un dict "metrics" (Loventre Metrics Bus),
  - applicare il Policy Bridge (safe/borderline/critical/invalid + spiegazione),
  - scrivere su disco un nuovo JSON arricchito con i campi globali:

        "global_decision_label"
        "global_decision_score"
        "global_meta_explanation"

Uso tipico:

  python3 loventre_metrics_enrich_with_policy_bridge.py \
      --input metrics_TSP_crit28_demo.json

  -> produce per default:
     metrics_TSP_crit28_demo_with_global.json

Può essere usato come:
  - ponte verso Coq (file pronto come witness metrico),
  - archivio di snapshot Loventre (seed di stato su singole istanze).
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Dict

import loventre_policy_bridge as lpb


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


def load_metrics(path: Path) -> Dict[str, Any]:
    """Carica un dict metrics da un file JSON."""
    if not path.exists():
        raise FileNotFoundError(f"File non trovato: {path}")
    with path.open("r", encoding="utf-8") as f:
        data = json.load(f)
    if not isinstance(data, dict):
        raise ValueError("Il JSON non contiene un oggetto/dict alla radice.")
    return data


def save_metrics(path: Path, metrics: Dict[str, Any]) -> None:
    """Salva il dict metrics in un file JSON (pretty-printed)."""
    with path.open("w", encoding="utf-8") as f:
        json.dump(metrics, f, indent=2, sort_keys=True, ensure_ascii=False)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Arricchisce un file metrics JSON con il Policy Bridge "
            "(global_decision_label / score / explanation)."
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
            "Se non specificato, usa '<input_basename>_with_global.json'."
        ),
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()

    input_path = Path(args.input)
    if args.output is not None:
        output_path = Path(args.output)
    else:
        # Costruiamo automaticamente un nome tipo "foo_with_global.json"
        stem = input_path.stem  # es. "metrics_TSP_crit28_demo"
        suffix = input_path.suffix or ".json"
        output_path = input_path.with_name(f"{stem}_with_global{suffix}")

    print(f"[INFO] Input  metrics JSON : {input_path}")
    print(f"[INFO] Output metrics JSON : {output_path}")

    metrics = load_metrics(input_path)
    metrics = _apply_policy_bridge(metrics)
    save_metrics(output_path, metrics)

    print("[OK] Metrics arricchiti con Policy Bridge e salvati.")
    print("     Campi aggiunti attesi:")
    print("       - global_decision_label")
    print("       - global_decision_score")
    print("       - global_meta_explanation")


if __name__ == "__main__":
    main()

