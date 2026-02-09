#!/usr/bin/env python3
# ============================================================
# LOVENTRE ENGINE — GCT FAMILY SIGNATURE v5.7
# ============================================================
#  - Costruisce una firma strutturale per ogni famiglia
#  - Usa solo informazioni GCT (non numeriche)
#  - Invariante rispetto a scaling, rumore, parametri
#  - NON prende decisioni
#  - NON altera policy
#  - OUTPUT deterministico e non imitabile
# ============================================================

import json
import sys
from pathlib import Path
from collections import Counter
from typing import Dict, Optional

# ------------------------------------------------------------
# Path canonico: root del Loventre Engine
# ------------------------------------------------------------
ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from loventre_metrics_bus import ensure_loventre_keys  # noqa: E402


# ------------------------------------------------------------
# Famiglie canoniche (stesse di v5.5)
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


def build_signature(counter: Counter) -> str:
    """
    Costruisce una firma GCT canonica.
    """
    if not counter:
        return "GCT::EMPTY"

    total = sum(counter.values())
    dominant, dom_count = counter.most_common(1)[0]

    if dominant == "GCT_INCONCLUSIVE":
        return "GCT::PRE_GLOBAL::INCONCLUSIVE"

    if dominant == "GCT_CONDUCTANCE_COLLAPSE":
        if dom_count == total:
            return "GCT::COLLAPSE::STABLE"
        else:
            return "GCT::COLLAPSE::MIXED"

    if dominant == "GCT_MONODROMY_OBSTRUCTION":
        return "GCT::MONODROMY"

    if dominant == "GCT_CRITICAL_INTERFACE":
        return "GCT::CRITICAL_INTERFACE"

    return f"GCT::OTHER::{dominant}"


# ------------------------------------------------------------
# Main
# ------------------------------------------------------------

def main() -> None:
    signatures = {}

    print("\n=== GCT FAMILY SIGNATURE (v5.7) ===\n")

    for fam, files in FAMILIES.items():
        counter = Counter()

        for fname in files:
            path = ROOT / fname
            if not path.exists():
                continue

            metrics = load_metrics(path)
            if metrics is None:
                continue

            gct = metrics.get("gct_barrier")
            if gct is not None:
                counter[gct] += 1

        signature = build_signature(counter)
        signatures[fam] = signature

        print(f"[{fam}]")
        print(f"  signature : {signature}")
        print(f"  histogram : {dict(counter)}\n")

    out = ROOT / "gct_family_signature.json"
    out.write_text(json.dumps(signatures, indent=2, sort_keys=True))
    print(f"→ Salvato {out.name}\n")


if __name__ == "__main__":
    main()

