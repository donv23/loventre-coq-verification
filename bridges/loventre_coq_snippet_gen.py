"""
loventre_coq_snippet_gen.py
----------------------------------------------------------
Genera automaticamente snippet Coq (Definition ... : LMetrics := {| ... |}.)
a partire dai JSON in witness_json/.

Ogni JSON deve rispettare lo schema LMetricsWitnessJSON definito
in loventre_json_schema.py.

Output:
  - Stampa a video uno snippet Coq per ciascun witness.
  - (facoltativo in futuro: scrittura in file .v)

Autore: Vincenzo Loventre — Dicembre 2025
"""

from __future__ import annotations
import json
from pathlib import Path
from typing import Any, Dict

from loventre_json_schema import LMetricsWitnessJSON, load_witness_json

ROOT = Path(__file__).parent
WITNESS_DIR = ROOT / "witness_json"


# ---------------------------------------------------------------------------
# Utilità
# ---------------------------------------------------------------------------

def fmt_value(v: Any) -> str:
    """Converte un valore Python in rappresentazione Coq-friendly."""
    if v is None:
        return "_ (* TODO: fill *)"
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, (int, float)):
        # formato con max 6 cifre significative
        return f"{v:.6g}"
    if isinstance(v, str):
        # time_regime, risk_class, ecc.
        if v.startswith("time_"):
            return v
        if v.startswith("risk_"):
            return v
        if v.startswith("meta_"):
            return v
        if v.startswith("GD_"):
            return v
        if v.startswith("GC_"):
            return v
        return f"\"{v}\""
    return f"(* unsupported type {type(v).__name__} *) _"


def gen_coq_snippet(w: LMetricsWitnessJSON) -> str:
    """Genera il testo Coq per una singola Definition a partire da un witness."""
    lines = []
    lines.append(f"(* Auto-generated from witness JSON for definition {w.lm_id} *)")
    lines.append(f"Definition {w.lm_id} : LMetrics :=")
    lines.append("  {|")

    for key, val in w.metrics.items():
        lines.append(f"    {key} := {fmt_value(val)};")

    lines.append("  |}.")
    lines.append("(* End of auto-generated snippet. *)\n")
    return "\n".join(lines)


def main() -> None:
    """Legge tutti i witness_json/*.json e genera snippet Coq."""
    print("=== LOVENTRE COQ SNIPPET GENERATOR ===")
    print(f"Root motore   : {ROOT}")
    print(f"Directory JSON: {WITNESS_DIR}\n")

    if not WITNESS_DIR.exists():
        print("[WARN] Directory witness_json non trovata.")
        return

    files = sorted(WITNESS_DIR.glob("*.json"))
    if not files:
        print("[WARN] Nessun JSON trovato in witness_json/")
        return

    for path in files:
        try:
            w = load_witness_json(path, validate=False)
        except Exception as e:
            print(f"[ERRORE] Impossibile caricare {path.name}: {e}")
            continue

        print("========================================================================")
        print(f"=== SNIPPET COQ per {path.name} ===")
        print("========================================================================")
        print(gen_coq_snippet(w))
        print("")


if __name__ == "__main__":
    main()

