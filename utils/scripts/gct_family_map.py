#!/usr/bin/env python3
# ============================================================
# LOVENTRE ENGINE — GCT FAMILY MAP v5.5 (PYTHON SAFE)
# ============================================================
#  - Aggrega la Global Coherence Trichotomy per famiglie
#  - Usa esclusivamente metrics JSON canonici
#  - Forza ensure_loventre_keys (bus v5.4+)
#  - NON prende decisioni
#  - NON altera policy
#  - SOLO diagnostica strutturale
# ============================================================

import json
import sys
from pathlib import Path
from collections import Counter
from typing import Optional, Dict

# ------------------------------------------------------------
# Path canonico: root del Loventre Engine
# ------------------------------------------------------------
ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from loventre_metrics_bus import ensure_loventre_keys  # noqa: E402


# ------------------------------------------------------------
# Famiglie canoniche (witness fissi)
# ------------------------------------------------------------

FAMILIES = {
    "2SAT_easy": [
        "metrics_2SAT_easy_demo.json",
    ],
    "2SAT_crit": [
        "metrics_2SAT_crit_demo.json",
    ],
    "SATcrit16": [
        "metrics_SAT_crit16_demo.json",
    ],
    "TSPcrit28": [
        "metrics_TSP_crit28_demo.json",
    ],
    "seed_grid": [
        "metrics_seed_grid_demo_global.json",
    ],
}


# ------------------------------------------------------------
# Utility
# ------------------------------------------------------------

def load_metrics(path: Path) -> Optional[Dict]:
    try:
        data = json.loads(path.read_text())
        if not isinstance(data, dict):
            return None
        return ensure_loventre_keys(data)
    except Exception:
        return None


# ------------------------------------------------------------
# Main
# ------------------------------------------------------------

def main() -> None:
    summary = {}

    print("\n=== GCT FAMILY MAP (v5.5) ===\n")

    for fam, files in FAMILIES.items():
        counter = Counter()

        for fname in files:
            path = ROOT / fname
            if not path.exists():
                counter["MISSING"] += 1
                continue

            metrics = load_metrics(path)
            if metrics is None:
                counter["INVALID"] += 1
                continue

            gct = metrics.get("gct_barrier")
            if gct is None:
                counter["UNKNOWN"] += 1
            else:
                counter[gct] += 1

        summary[fam] = dict(counter)

        print(f"[{fam}]")
        for k, v in summary[fam].items():
            print(f"  {k}: {v}")
        print()

    out = ROOT / "gct_family_map_summary.json"
    out.write_text(json.dumps(summary, indent=2, sort_keys=True))
    print(f"→ Salvato {out.name}\n")


if __name__ == "__main__":
    main()

