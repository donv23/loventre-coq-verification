#!/usr/bin/env python3
# ============================================================
# LOVENTRE ENGINE — GCT FAMILY DYNAMICS v5.6
# ============================================================
#  - Analizza l'evoluzione della barriera GCT lungo una famiglia
#  - Ordina i metrics per parametro (quando presente)
#  - Evidenzia transizioni strutturali
#  - NON prende decisioni
#  - NON altera policy
#  - SOLO diagnostica strutturale
# ============================================================

import json
import sys
from pathlib import Path
from collections import Counter
from typing import List, Dict, Optional

# ------------------------------------------------------------
# Path canonico: root del Loventre Engine
# ------------------------------------------------------------
ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from loventre_metrics_bus import ensure_loventre_keys  # noqa: E402


# ------------------------------------------------------------
# Configurazione famiglie dinamiche
# ------------------------------------------------------------

DYNAMIC_FAMILIES = {
    "seed_grid": [
        "metrics_seed_grid_demo_global.json",
    ],
    "2SAT_sweep": [
        "metrics_2SAT_easy_demo.json",
        "metrics_2SAT_crit_demo.json",
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


def extract_order_key(metrics: Dict) -> float:
    """
    Estrae una chiave di ordinamento:
    - prova con chi_compactness
    - fallback su kappa_eff
    """
    for key in ("chi_compactness", "kappa_eff"):
        try:
            val = metrics.get(key)
            if val is not None:
                return float(val)
        except Exception:
            pass
    return 0.0


# ------------------------------------------------------------
# Main
# ------------------------------------------------------------

def main() -> None:
    print("\n=== GCT FAMILY DYNAMICS (v5.6) ===\n")

    for fam, files in DYNAMIC_FAMILIES.items():
        records: List[Dict] = []

        for fname in files:
            path = ROOT / fname
            if not path.exists():
                continue

            metrics = load_metrics(path)
            if metrics is None:
                continue

            records.append(metrics)

        if not records:
            print(f"[{fam}] nessun dato valido\n")
            continue

        # Ordina per parametro strutturale
        records.sort(key=extract_order_key)

        print(f"[{fam}]")
        last_gct = None
        transitions = Counter()

        for idx, m in enumerate(records):
            gct = m.get("gct_barrier") or "UNKNOWN"
            key = extract_order_key(m)

            print(f"  step {idx:02d} | key={key:.3f} | GCT={gct}")

            if last_gct is not None and gct != last_gct:
                transitions[(last_gct, gct)] += 1

            last_gct = gct

        if transitions:
            print("  -- transizioni rilevate:")
            for (a, b), c in transitions.items():
                print(f"     {a} → {b} : {c}")
        else:
            print("  -- nessuna transizione GCT")

        print()

    print("=== FINE GCT FAMILY DYNAMICS ===\n")


if __name__ == "__main__":
    main()

