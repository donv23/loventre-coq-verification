"""
loventre_export_witness_json.py

Esporta i witness canonici LMetrics (m_seed11_cli_demo, m_TSPcrit28_cli_demo, ...)
in formato JSON stabile, usando lo schema definito in loventre_json_schema.py.

Input:
  - metrics_seed11_cli_demo.json
  - metrics_TSP_crit28_demo.json
  - metrics_SAT_crit16_demo.json
  - metrics_seed_grid_demo_global.json

Output:
  - witness_json/m_seed11_cli_demo.json
  - witness_json/m_TSPcrit28_cli_demo.json
  - witness_json/m_SATcrit16_cli_demo.json
  - witness_json/m_seed_grid_demo.json

Lo script è pensato come "ponte interno" fra:
  - i JSON di metriche usati dal motore,
  - lo schema LMetricsWitnessJSON,
  - il mondo Coq (Loventre_LMetrics_JSON_Witness.v).
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Dict

from loventre_json_schema import (
    LMETRICS_METRIC_KEYS,
    make_witness_json,
    save_witness_json,
)


# ---------------------------------------------------------------------------
# 1. Specifiche dei witness da esportare
# ---------------------------------------------------------------------------

ROOT = Path(__file__).parent

#: Mappa fra lm_id (lato Coq) e file metrics JSON + meta-info.
WITNESS_EXPORT_SPECS = {
    "m_seed11_cli_demo": {
        "metrics_json": ROOT / "metrics_seed11_cli_demo.json",
        "role": "P_like_SAFE_low",  # coerente con COQ_WITNESS_ROLES
        "tags": {
            "family": "seed",
            "kind": "P_like",
            "note": "CLI demo seed11 / P_like SAFE/LOW",
        },
    },
    "m_TSPcrit28_cli_demo": {
        "metrics_json": ROOT / "metrics_TSP_crit28_demo.json",
        "role": "NP_like_black_hole_TSP",
        "tags": {
            "family": "TSP_crit_n",
            "kind": "NP_like_black_hole",
            "n_cities": 28,
            "note": "TSP_crit_n demo / NP_like-black-hole",
        },
    },
    "m_SATcrit16_cli_demo": {
        "metrics_json": ROOT / "metrics_SAT_crit16_demo.json",
        "role": "NP_like_black_hole_SAT",
        "tags": {
            "family": "SAT_crit_n",
            "kind": "NP_like_black_hole",
            "instance": "sat_crit16",
            "note": "SAT_crit_n demo / NP_like-black-hole",
        },
    },
    "m_seed_grid_demo": {
        "metrics_json": ROOT / "metrics_seed_grid_demo_global.json",
        "role": "P_like_accessible_borderline",
        "tags": {
            "family": "seed_grid",
            "kind": "P_like_accessible",
            "note": "Seed grid demo / P_like_accessibile borderline",
        },
    },
}


# ---------------------------------------------------------------------------
# 2. Estrazione robusta del bus di metriche dai JSON esistenti
# ---------------------------------------------------------------------------

def extract_metrics_from_raw(data: Any) -> Dict[str, Any]:
    """
    Data una struttura JSON arbitraria (già caricata), estrae un dict di metriche
    che contenga almeno le chiavi canoniche LMETRICS_METRIC_KEYS, se possibile.

    Strategia:
      1. Se esiste data["metrics"] ed è un dict, usiamo quello.
      2. Altrimenti, prendiamo tutte le (k, v) al top-level tali che
         k sia in LMETRICS_METRIC_KEYS.
      3. Se ancora vuoto, e data è un dict piatto con valori scalari,
         usiamo tutto data come metrics (fallback difensivo).

    Le chiavi mancanti rispetto a LMETRICS_METRIC_KEYS verranno riempite a None
    più avanti, così lo schema JSON resta sempre completo.
    """
    if not isinstance(data, dict):
        raise ValueError(
            "Il JSON di input deve essere un oggetto (dict), trovato: "
            f"{type(data)!r}"
        )

    # Caso 1: campo 'metrics' esplicito
    metrics_field = data.get("metrics")
    if isinstance(metrics_field, dict):
        metrics = dict(metrics_field)
    else:
        # Caso 2: filtra per chiavi canoniche
        metrics = {k: data[k] for k in LMETRICS_METRIC_KEYS if k in data}

        # Caso 3: se ancora vuoto, prova a usare tutto data (se 'piatto')
        if not metrics:
            if all(
                not isinstance(v, (dict, list))
                for v in data.values()
            ):
                metrics = dict(data)

    return metrics


# ---------------------------------------------------------------------------
# 3. Pipeline di esportazione
# ---------------------------------------------------------------------------

def export_all_witness_json(output_dir: Path) -> None:
    """
    Esporta tutti i witness definiti in WITNESS_EXPORT_SPECS in output_dir.
    """
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    print("=== LOVENTRE EXPORT WITNESS JSON ===")
    print(f"Root motore      : {ROOT}")
    print(f"Output directory : {output_dir}")
    print("")

    for lm_id, spec in WITNESS_EXPORT_SPECS.items():
        metrics_path: Path = spec["metrics_json"]
        role: str = spec["role"]
        tags: Dict[str, Any] = dict(spec.get("tags", {}))

        print(f"[WITNESS] lm_id = {lm_id}")
        print(f"  metrics JSON : {metrics_path}")

        if not metrics_path.exists():
            print(f"  [WARN] File metrics non trovato, salto questo witness.")
            print("")
            continue

        # Carica il JSON grezzo
        with metrics_path.open("r", encoding="utf-8") as f:
            raw_data = json.load(f)

        metrics = extract_metrics_from_raw(raw_data)

        # Garantiamo che tutte le chiavi canoniche esistano (anche a None)
        for key in LMETRICS_METRIC_KEYS:
            metrics.setdefault(key, None)

        # Aggiungi nei tag un riferimento al file di origine
        tags.setdefault("metrics_json_source", metrics_path.name)

        witness = make_witness_json(
            lm_id=lm_id,
            metrics=metrics,
            role=role,
            source="loventre_engine_clean_seed_v3",
            tags=tags,
            validate=False,  # la completezza è forzata dal setdefault sopra
        )

        out_path = output_dir / f"{lm_id}.json"
        save_witness_json(witness, out_path)

        print(f"  [OK] Esportato in: {out_path}")
        print("")

    print("=== FINE EXPORT WITNESS JSON ===")


def main() -> None:
    """
    Entry point CLI minimale.
    """
    output_dir = ROOT / "witness_json"
    export_all_witness_json(output_dir)


if __name__ == "__main__":
    main()

