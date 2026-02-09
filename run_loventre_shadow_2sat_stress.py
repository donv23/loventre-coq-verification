"""
run_loventre_shadow_2sat_stress.py

Shadow stress test per Loventre Engine.
Verifica collasso + isteresi diagnostica.

NON modifica il CANON.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Dict, Any, List

from loventre_hysteresis_diagnostic import detect_hysteresis


SHADOW_JSONS = [
    "metrics_2SAT_easy_demo_hysteresis.json",
    "metrics_2SAT_easy_demo_blackhole.json",
]


def load_json(path: Path) -> Dict[str, Any]:
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def main() -> int:
    base_dir = Path(__file__).resolve().parent
    failed: List[str] = []

    print("\n[Loventre][SHADOW] Avvio stress test isteresi + collasso\n")

    for filename in SHADOW_JSONS:
        path = base_dir / filename
        label = f"SHADOW:{filename}"

        if not path.exists():
            print(f"[FAIL] {label} – file non trovato")
            failed.append(filename)
            continue

        metrics = load_json(path)
        metrics = detect_hysteresis(metrics)

        lg = metrics.get("loventre_global", {}) or {}
        decision = lg.get("global_decision")
        hysteresis = metrics.get("hysteresis_detected")

        print(f"[CHECK] {filename}")
        print(f"        decision={decision}, hysteresis_detected={hysteresis}")

        if decision != "BLACKHOLE":
            print(f"[FAIL] {label} – atteso BLACKHOLE, trovato {decision}")
            failed.append(filename)

        if filename.endswith("_hysteresis.json") and hysteresis is not True:
            print(f"[FAIL] {label} – isteresi attesa ma non rilevata")
            failed.append(filename)

        print("-" * 60)

    if failed:
        print("\n[Loventre][SHADOW] TEST FALLITO")
        for f in failed:
            print(f"  - {f}")
        print()
        return 1

    print("\n[Loventre][SHADOW] TEST OK – isteresi diagnosticata correttamente\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

