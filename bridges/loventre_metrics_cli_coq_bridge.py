#!/usr/bin/env python3
"""
Loventre CLI Bridge (dicembre 2025 — path-fix)

Estensione v5.3:
- stampa il regime operativo C_regime (se presente)
- SOLO reporting (nessun effetto su decisione o Coq)
"""

from __future__ import annotations

import argparse
import json
import sys
import pathlib
from pathlib import Path
from typing import Any, Dict

# --- PATH FIX per garantire il caricamento del modulo locale ---
ROOT = pathlib.Path(__file__).resolve().parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import loventre_policy_bridge as lpb
from loventre_project_metrics_to_lmetrics import project_metrics_to_lmetrics
from loventre_lmetrics_to_coq_snippet import FIELDS_ORDER, coq_of_field


def load_json(path: Path) -> Dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"File non trovato: {path}")
    with path.open("r", encoding="utf-8") as f:
        data = json.load(f)
    if not isinstance(data, dict):
        raise ValueError("JSON non valido.")
    return data


def apply_policy_bridge(metrics: Dict[str, Any]) -> Dict[str, Any]:
    if hasattr(lpb, "apply_policy_bridge_to_metrics"):
        return lpb.apply_policy_bridge_to_metrics(metrics)  # type: ignore
    if hasattr(lpb, "append_policy_bridge_to_metrics"):
        return lpb.append_policy_bridge_to_metrics(metrics)  # type: ignore
    raise RuntimeError("Modulo loventre_policy_bridge non espone funzioni compatibili.")


def emit_coq_snippet(def_name: str, lmetrics: Dict[str, Any]) -> None:
    print()
    print("========================================================================")
    print("=== Coq LMetrics snippet (auto-generated)                            ===")
    print("========================================================================")
    print(f"Definition {def_name} : LMetrics :=")
    print("  {|")
    for key in FIELDS_ORDER:
        expr = coq_of_field(key, lmetrics.get(key))
        print(f"    {key} := {expr};")
    print("  |}.")
    print("(* End of snippet. *)")


def print_report(
    metrics_enriched: Dict[str, Any],
    lmetrics: Dict[str, Any],
    metrics_name: str,
    def_name: str,
) -> None:
    print("========================================================================")
    print("=== LOVENTRE METRICS → POLICY BRIDGE → LMetrics → Coq (CLI)         ===")
    print("========================================================================")
    print(f"Source metrics JSON : {metrics_name}")
    print(f"Coq Definition name : {def_name}")
    print()

    # --- REGIME OPERATIVO (C) — SOLO REPORTING ---
    C_regime = metrics_enriched.get("C_regime")
    if C_regime is not None:
        print(f"Regime operativo (C) : {C_regime}")
    else:
        print("Regime operativo (C) : non determinato")

    print()

    lg = metrics_enriched.get("loventre_global")
    print("Blocco operative loventre_global:")
    if isinstance(lg, dict):
        print(f"  decision : {lg.get('global_decision')}")
        print(f"  color    : {lg.get('global_color')}")
        print(f"  score    : {lg.get('global_score')}")
    else:
        print("  (nessun blocco trovato)")

    print()
    emit_coq_snippet(def_name, lmetrics)


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Loventre CLI Bridge")
    p.add_argument("--metrics-json", "-m", required=True)
    p.add_argument("--def-name", "-n", default=None)
    return p.parse_args()


def main() -> None:
    args = parse_args()
    metrics_path = Path(args.metrics_json)
    metrics = load_json(metrics_path)
    def_name = args.def_name or f"m_from_{metrics_path.stem}"
    metrics_enriched = apply_policy_bridge(metrics)
    lmetrics = project_metrics_to_lmetrics(metrics_enriched)
    print_report(metrics_enriched, lmetrics, metrics_path.name, def_name)


if __name__ == "__main__":
    main()

