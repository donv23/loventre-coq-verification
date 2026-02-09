#!/usr/bin/env python3
"""
Loventre Engine – LMetrics Witness Profile (v2 bridge)

Costruisce una tabella Markdown con il profilo operativo dei witness
LMetrics a partire dai file metrics_*.json nella root del motore.
"""

import json
import pathlib
from typing import Any, Dict, List


ROOT = pathlib.Path(__file__).resolve().parent
OUTPUT = ROOT / "LOVENTRE_LMetrics_Witness_Profile.md"


def load_json(path: pathlib.Path) -> Any:
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def extract_metrics(data: Any) -> Dict[str, Any]:
    """
    Alcuni JSON potrebbero avere una chiave "metrics".
    Se presente, usiamo quella; altrimenti usiamo il dict top-level.
    """
    if isinstance(data, dict):
        inner = data.get("metrics")
        if isinstance(inner, dict):
            return inner
        return data
    return {}


def get_first_non_empty(m: Dict[str, Any], keys: List[str], default: str = "") -> str:
    for k in keys:
        if k in m and m[k] is not None:
            return str(m[k])
    return default


def build_rows() -> List[Dict[str, str]]:
    rows: List[Dict[str, str]] = []
    metrics_files = sorted(ROOT.glob("metrics_*.json"))

    for path in metrics_files:
        try:
            data = load_json(path)
            m = extract_metrics(data)
        except Exception as e:
            rows.append(
                {
                    "file": path.name,
                    "family": "ERROR",
                    "meta_label": f"JSON error: {e}",
                    "risk_class": "",
                    "horizon_flag": "",
                    "time_regime": "",
                    "loventre_global_decision": "",
                    "loventre_global_color": "",
                    "loventre_global_score": "",
                    "phase_hint": "",
                }
            )
            continue

        row = {
            "file": path.name,
            "family": get_first_non_empty(
                m, ["family", "family_label", "metrics_family"], ""
            ),
            "meta_label": get_first_non_empty(m, ["meta_label"], ""),
            "risk_class": get_first_non_empty(m, ["risk_class"], ""),
            "horizon_flag": get_first_non_empty(m, ["horizon_flag"], ""),
            "time_regime": get_first_non_empty(m, ["time_regime"], ""),
            "loventre_global_decision": get_first_non_empty(
                m, ["loventre_global_decision"], ""
            ),
            "loventre_global_color": get_first_non_empty(
                m, ["loventre_global_color"], ""
            ),
            "loventre_global_score": get_first_non_empty(
                m, ["loventre_global_score"], ""
            ),
            "phase_hint": get_first_non_empty(
                m, ["phase_hint", "phase_label"], ""
            ),
        }
        rows.append(row)

    return rows


def write_markdown(rows: List[Dict[str, str]]) -> None:
    with OUTPUT.open("w", encoding="utf-8") as f:
        f.write("# LOVENTRE_LMetrics_Witness_Profile\n")
        f.write("\n")
        f.write("_Profilo operativo dei witness LMetrics (Python → Coq v2)_\n")
        f.write("\n")

        if not rows:
            f.write("\n(Nessun file metrics_*.json trovato.)\n")
            return

        headers = [
            "file",
            "family",
            "meta_label",
            "risk_class",
            "horizon_flag",
            "time_regime",
            "loventre_global_decision",
            "loventre_global_color",
            "loventre_global_score",
            "phase_hint",
        ]

        f.write("| " + " | ".join(headers) + " |\n")
        f.write("|" + "|".join(["---"] * len(headers)) + "|\n")

        for r in rows:
            values = [
                r.get("file", ""),
                r.get("family", ""),
                r.get("meta_label", ""),
                r.get("risk_class", ""),
                r.get("horizon_flag", ""),
                r.get("time_regime", ""),
                r.get("loventre_global_decision", ""),
                r.get("loventre_global_color", ""),
                r.get("loventre_global_score", ""),
                r.get("phase_hint", ""),
            ]
            safe_values = [v.replace("|", "/") for v in values]
            f.write("| " + " | ".join(safe_values) + " |\n")

    print(f"Scritto {OUTPUT.name} con {len(rows)} righe.")


def main() -> None:
    rows = build_rows()
    write_markdown(rows)


if __name__ == "__main__":
    main()

