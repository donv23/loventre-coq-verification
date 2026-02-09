#!/usr/bin/env python3
"""
LOVENTRE ENGINE – LMetrics JSON -> Coq snippet (LMetrics record)
================================================================

Scopo:
  - leggere un file JSON LMetrics-like (es. lmetrics_TSP_crit28_example.json),
  - generare su stdout una definizione Coq del tipo:

        Definition m_TSPcrit28_json : LMetrics :=
          {|
            kappa_eff := 0.95;
            entropy_eff := 0.93;
            ...
          |}.

  - fare una mappatura ragionevole da stringhe JSON a costruttori Coq per:

        time_regime, risk_class, meta_label,
        loventre_global_decision, loventre_global_color.

Note:
  - per i numeri usiamo direttamente la notazione decimale (es. 0.95);
    lato Coq basterà avere `Open Scope R_scope.` o simile.
  - se una stringa non è riconosciuta, usiamo costruttori *_unknown
    o mettiamo un commento con TODO.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Dict

FIELDS_ORDER = [
    "kappa_eff",
    "entropy_eff",
    "V0",
    "a_min",
    "p_tunnel",
    "P_success",
    "gamma_dilation",
    "time_regime",
    "mass_eff",
    "inertial_idx",
    "risk_index",
    "risk_class",
    "meta_label",
    "chi_compactness",
    "horizon_flag",
    "loventre_global_decision",
    "loventre_global_color",
    "loventre_global_score",
]


def coq_of_bool(b: bool) -> str:
    return "true" if b else "false"


def coq_of_number(x: Any) -> str:
    # Supponiamo che sia int o float; usiamo la forma testuale diretta.
    # In Coq, con R_scope, 0.95 è interpretato come un reale.
    return repr(x)


def coq_time_regime(s: str) -> str:
    s = s.strip()
    if s in ("time_euclidean", "time_threshold", "time_hyperbolic"):
        return s
    return "time_unknown"


def coq_risk_class(s: str) -> str:
    s = s.strip()
    if s == "LOW":
        return "risk_LOW"
    if s == "MEDIUM":
        return "risk_MEDIUM"
    if s == "NP_like_critico":
        return "risk_NP_like_critico"
    if s == "NP_like_black_hole":
        return "risk_NP_like_black_hole"
    return "risk_UNKNOWN"


def coq_meta_label(s: str) -> str:
    s = s.strip()
    if s == "P_like_like":
        return "meta_P_like_like"
    if s == "NP_like_critico":
        return "meta_NP_like_critico"
    if s == "NP_like_black_hole":
        return "meta_NP_like_black_hole"
    return "meta_unknown"


def coq_global_decision(s: str) -> str:
    s = s.strip()
    # Se il JSON contiene già "GD_critical" etc., usiamo quello
    if s.startswith("GD_"):
        return s
    # Altrimenti proviamo a mappare da safe/borderline/critical/invalid
    z = s.lower()
    if z == "safe":
        return "GD_safe"
    if z == "borderline":
        return "GD_borderline"
    if z == "critical":
        return "GD_critical"
    if z == "invalid":
        return "GD_invalid"
    return "GD_invalid"


def coq_global_color(s: str) -> str:
    s = s.strip()
    # Se il JSON contiene già "GC_red" etc., usiamo quello
    if s.startswith("GC_"):
        return s
    z = s.upper()
    if z == "GREEN":
        return "GC_green"
    if z == "AMBER":
        return "GC_amber"
    if z == "RED":
        return "GC_red"
    return "GC_unknown"


def coq_of_field(key: str, value: Any) -> str:
    """Mappa un campo JSON a una espressione Coq."""
    if value is None:
        return "_ (* TODO: fill *)"

    if key == "time_regime" and isinstance(value, str):
        return coq_time_regime(value)

    if key == "risk_class" and isinstance(value, str):
        return coq_risk_class(value)

    if key == "meta_label" and isinstance(value, str):
        return coq_meta_label(value)

    if key == "loventre_global_decision" and isinstance(value, str):
        return coq_global_decision(value)

    if key == "loventre_global_color" and isinstance(value, str):
        return coq_global_color(value)

    if isinstance(value, bool):
        return coq_of_bool(value)

    if isinstance(value, (int, float)):
        return coq_of_number(value)

    if isinstance(value, str):
        # Stringa generica che non sappiamo mappare: commento + TODO.
        return f'(* from JSON: "{value}" *) _'

    # fallback generico
    return "_ (* unsupported type *)"


def load_lmetrics(path: Path) -> Dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"File non trovato: {path}")
    with path.open("r", encoding="utf-8") as f:
        data = json.load(f)
    if not isinstance(data, dict):
        raise ValueError("Il JSON non contiene un oggetto/dict alla radice.")
    return data


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Genera una snippet Coq (LMetrics record) a partire da un JSON LMetrics-like."
        )
    )
    parser.add_argument(
        "--input",
        "-i",
        required=True,
        help="Percorso al file JSON LMetrics-like (es. lmetrics_TSP_crit28_example.json).",
    )
    parser.add_argument(
        "--name",
        "-n",
        default=None,
        help=(
            "Nome Coq per la Definition (es. m_TSPcrit28_json). "
            "Se non specificato, usa m_from_<basename>."
        ),
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()

    input_path = Path(args.input)
    lmetrics = load_lmetrics(input_path)

    if args.name is not None:
        def_name = args.name
    else:
        stem = input_path.stem  # es. "lmetrics_TSP_crit28_example"
        def_name = f"m_from_{stem}"

    print(f"(* Auto-generated from {input_path.name} *)")
    print(f"Definition {def_name} : LMetrics :=")
    print("  {|")

    for key in FIELDS_ORDER:
        coq_expr = coq_of_field(key, lmetrics.get(key))
        # Coq accetta il ';' anche sull'ultimo campo
        print(f"    {key} := {coq_expr};")

    print("  |}.")


if __name__ == "__main__":
    main()

