"""
loventre_witness_json_inspect.py

Utility di ispezione per i witness LMetrics in formato JSON
(witness_json/*.json), basati sullo schema definito in
loventre_json_schema.py.

Scopo:
- Caricare tutti i witness JSON disponibili.
- Stampare un riassunto compatto per ciascun witness, evidenziando:
    * lm_id, role, family/kind,
    * meta_label, risk_class, horizon_flag,
    * time_regime, p_tunnel, risk_index, chi_compactness.

Questo script non modifica nulla: è solo uno "specchio" leggibile
per verificare che i witness JSON siano coerenti con il modello Loventre
e con i ruoli P_like / P_acc / NP_like-black-hole che usiamo in Coq.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any, Dict

from loventre_json_schema import (
    LMetricsWitnessJSON,
    load_witness_json,
)


ROOT = Path(__file__).parent
WITNESS_DIR = ROOT / "witness_json"


def _safe_get(metrics: Dict[str, Any], key: str, default: Any = None) -> Any:
    """Helper per estrarre una chiave da metrics con default."""
    return metrics.get(key, default)


def print_witness_summary(path: Path) -> None:
    """
    Carica un witness JSON e stampa un riassunto compatto.
    """
    w: LMetricsWitnessJSON = load_witness_json(path, validate=False)
    m = w.metrics
    t = w.tags

    family = t.get("family", "unknown_family")
    kind = t.get("kind", "unknown_kind")

    risk_class = _safe_get(m, "risk_class", "unknown_risk")
    meta_label = _safe_get(m, "meta_label", "unknown_meta")
    horizon_flag = _safe_get(m, "horizon_flag", None)
    time_regime = _safe_get(m, "time_regime", "unknown_time_regime")

    p_tunnel = _safe_get(m, "p_tunnel", None)
    risk_index = _safe_get(m, "risk_index", None)
    chi_compactness = _safe_get(m, "chi_compactness", None)

    print("========================================================================")
    print(f"=== WITNESS JSON: {path.name} ===")
    print("========================================================================")
    print(f"lm_id   : {w.lm_id}")
    print(f"role    : {w.role}")
    print(f"family  : {family}")
    print(f"kind    : {kind}")
    print(f"source  : {w.source}")
    print("")
    print("Profilo Loventre (estratto dalle metriche):")
    print(f"  meta_label     : {meta_label}")
    print(f"  risk_class     : {risk_class}")
    print(f"  horizon_flag   : {horizon_flag}")
    print(f"  time_regime    : {time_regime}")
    print(f"  chi_compactness: {chi_compactness}")
    print(f"  risk_index     : {risk_index}")
    print(f"  p_tunnel       : {p_tunnel}")
    print("")
    print("Tags:")
    for k, v in sorted(t.items()):
        print(f"  - {k}: {v}")
    print("")


def main() -> None:
    """
    Entry point: ispeziona tutti i JSON in witness_json/.
    """
    print("=== LOVENTRE WITNESS JSON INSPECTOR ===")
    print(f"Root motore   : {ROOT}")
    print(f"Directory JSON: {WITNESS_DIR}")
    print("")

    if not WITNESS_DIR.exists():
        print("[WARN] Directory witness_json non esiste. Niente da ispezionare.")
        return

    json_files = sorted(WITNESS_DIR.glob("*.json"))
    if not json_files:
        print("[WARN] Nessun file .json trovato in witness_json.")
        return

    for path in json_files:
        print_witness_summary(path)


if __name__ == "__main__":
    main()

