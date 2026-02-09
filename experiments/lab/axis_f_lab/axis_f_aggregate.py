#!/usr/bin/env python3
"""
Axis F — Aggregated Structural Report (LAB)

Purpose:
- Aggregate Axis F classifications
- Produce descriptive statistics only
- No claims, no thresholds, no inference

LAB ONLY — This file does NOT modify the engine.
"""

import json
from pathlib import Path
from collections import defaultdict

WITNESS_DIR = Path("../witness_json")
OUTPUT_JSON = Path("AXIS_F_AGGREGATE_v1.json")
OUTPUT_MD = Path("AXIS_F_REPORT_v1.md")


def classify_entry(data):
    """
    Reproduce Axis F descriptive classification
    """
    result = {
        "NP_classical": "unknown",
        "NP_instance_profile": "unknown",
        "NP_structural_regime": "unknown",
    }

    name = data.get("name", "").lower()
    metrics = data.get("metrics", {})
    meta = data.get("meta", {})

    # Classical hint (descriptive, hardcoded)
    if "3sat" in name or "tsp" in name or "satcrit" in name:
        result["NP_classical"] = "NP-complete"
    elif "2sat" in name:
        result["NP_classical"] = "P"

    # Instance profile (heuristic, descriptive)
    curvature = metrics.get("kappa_eff")
    if isinstance(curvature, (int, float)):
        if curvature < -0.5:
            result["NP_instance_profile"] = "hard"
        elif curvature < 0:
            result["NP_instance_profile"] = "critical"
        else:
            result["NP_instance_profile"] = "easy"

    # Structural regime
    regime = meta.get("global_regime") or meta.get("meta_label")
    if isinstance(regime, str):
        result["NP_structural_regime"] = regime

    return result


def main():
    records = []
    stats = {
        "by_NP_classical": defaultdict(int),
        "by_instance_profile": defaultdict(int),
        "by_structural_regime": defaultdict(int),
        "cross_classical_vs_structural": defaultdict(int),
    }

    for path in sorted(WITNESS_DIR.glob("*.json")):
        try:
            data = json.loads(path.read_text())
        except Exception:
            continue

        classification = classify_entry(data)

        record = {
            "file": path.name,
            **classification,
        }
        records.append(record)

        stats["by_NP_classical"][classification["NP_classical"]] += 1
        stats["by_instance_profile"][classification["NP_instance_profile"]] += 1
        stats["by_structural_regime"][classification["NP_structural_regime"]] += 1

        key = (
            classification["NP_classical"],
            classification["NP_structural_regime"],
        )
        stats["cross_classical_vs_structural"][key] += 1

    aggregate = {
        "axis": "F",
        "status": "LAB_ONLY",
        "note": "Purely descriptive aggregation. No claims.",
        "total_files": len(records),
        "records": records,
        "statistics": {
            "by_NP_classical": dict(stats["by_NP_classical"]),
            "by_instance_profile": dict(stats["by_instance_profile"]),
            "by_structural_regime": dict(stats["by_structural_regime"]),
            "cross_classical_vs_structural": {
                f"{k[0]} | {k[1]}": v
                for k, v in stats["cross_classical_vs_structural"].items()
            },
        },
    }

    OUTPUT_JSON.write_text(json.dumps(aggregate, indent=2))

    # Markdown report
    lines = []
    lines.append("# Axis F — Aggregated Structural Report (LAB)\n")
    lines.append("**Status:** LAB ONLY\n")
    lines.append("**Nature:** Descriptive / Statistical\n")
    lines.append("\n---\n")
    lines.append(f"## Total files analyzed: {aggregate['total_files']}\n")

    def render_table(title, data):
        lines.append(f"\n### {title}\n")
        lines.append("| Category | Count |")
        lines.append("|----------|-------|")
        for k, v in sorted(data.items()):
            lines.append(f"| {k} | {v} |")

    render_table("By NP-classical label", aggregate["statistics"]["by_NP_classical"])
    render_table("By instance profile", aggregate["statistics"]["by_instance_profile"])
    render_table(
        "By structural regime", aggregate["statistics"]["by_structural_regime"]
    )

    lines.append("\n### Classical vs Structural (cross view)\n")
    lines.append("| NP-classical | Structural regime | Count |")
    lines.append("|--------------|-------------------|-------|")
    for k, v in sorted(aggregate["statistics"]["cross_classical_vs_structural"].items()):
        classical, structural = k.split(" | ")
        lines.append(f"| {classical} | {structural} | {v} |")

    lines.append("\n---\n")
    lines.append(
        "**Disclaimer:** This report is descriptive only. "
        "No equivalence, reduction, or separation claim is made."
    )

    OUTPUT_MD.write_text("\n".join(lines))


if __name__ == "__main__":
    main()

