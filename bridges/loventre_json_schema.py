"""
loventre_json_schema.py

Schema canonico per i JSON di witness LMetrics nel progetto LOVENTRE ENGINE.

Obiettivi:
- Definire un formato JSON stabile per i witness LMetrics (m_seed11, m_TSPcrit28, ecc.).
- Separare chiaramente:
    * identità del witness (lm_id, role),
    * metadati di sorgente (source, tags),
    * bus di metriche (metrics dict con chiavi canoniche).
- NON dipendere dall'implementazione interna del motore (solo stdlib).

Questo modulo può essere usato da altri componenti per:
- serializzare un bus di metriche in JSON,
- deserializzare e validare un JSON di witness,
- mantenere allineamento concettuale con i witness Coq in
  Loventre_LMetrics_JSON_Witness.v.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional


# ---------------------------------------------------------------------------
# 1. Chiavi canoniche del bus di metriche LMetrics
# ---------------------------------------------------------------------------

#: Lista ordinata delle chiavi "canoniche" del bus di metriche LMetrics.
#: Queste chiavi sono pensate per restare stabili a lungo termine
#: e corrispondono, a grandi linee, ai campi del record LMetrics lato Coq.
LMETRICS_METRIC_KEYS: List[str] = [
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
    "chi_compactness",
    "horizon_flag",
    "meta_label",
    "loventre_global_decision",
    "loventre_global_color",
]


# ---------------------------------------------------------------------------
# 2. Mappa dei witness "canonici" LMetrics (lato motore / JSON)
# ---------------------------------------------------------------------------

#: Witness principali, in corrispondenza con Loventre_LMetrics_JSON_Witness.v.
#: Questi identificatori sono usati sia nel motore Python (JSON) sia nel
#: mondo Coq come parametri di tipo LMetrics.
COQ_WITNESS_ROLES: Dict[str, str] = {
    "m_seed11_cli_demo": "P_like_SAFE_low",
    "m_seed_grid_demo": "P_like_accessible_borderline",
    "m_TSPcrit28_cli_demo": "NP_like_black_hole_TSP",
    "m_SATcrit16_cli_demo": "NP_like_black_hole_SAT",
}


# ---------------------------------------------------------------------------
# 3. Dataclass per il JSON di witness
# ---------------------------------------------------------------------------

@dataclass
class LMetricsWitnessJSON:
    """
    Rappresentazione ad alto livello di un witness LMetrics in formato JSON.

    Campi:
    - lm_id:   identificatore canonico del witness (es. 'm_TSPcrit28_cli_demo').
    - role:    ruolo/fase logica del witness (es. 'NP_like_black_hole_TSP').
    - source:  stringa che identifica la versione / sorgente del motore.
    - metrics: dizionario con il bus di metriche (chiavi in LMETRICS_METRIC_KEYS).
    - tags:    dizionario libero per metadati aggiuntivi (note, versione, ecc.).
    """

    lm_id: str
    role: str
    source: str
    metrics: Dict[str, Any]
    tags: Dict[str, Any]

    def to_ordered_dict(self) -> Dict[str, Any]:
        """
        Converte il witness in un dict con ordine di chiavi stabile:

        {
          "lm_id":   ...,
          "role":    ...,
          "source":  ...,
          "metrics": { ... chiavi LMETRICS_METRIC_KEYS in ordine ... },
          "tags":    { ... }
        }
        """
        ordered_metrics: Dict[str, Any] = {}
        # Inseriamo in ordine canonico; se una chiave manca, usiamo None.
        for key in LMETRICS_METRIC_KEYS:
            ordered_metrics[key] = self.metrics.get(key, None)

        # Conserviamo anche eventuali chiavi extra, in coda, in ordine alfabetico.
        for extra_key in sorted(k for k in self.metrics.keys() if k not in LMETRICS_METRIC_KEYS):
            ordered_metrics[extra_key] = self.metrics[extra_key]

        return {
            "lm_id": self.lm_id,
            "role": self.role,
            "source": self.source,
            "metrics": ordered_metrics,
            "tags": dict(self.tags) if self.tags is not None else {},
        }


# ---------------------------------------------------------------------------
# 4. Funzioni di validazione / costruzione
# ---------------------------------------------------------------------------

def validate_metrics_bus(metrics: Dict[str, Any]) -> None:
    """
    Controlla che il bus di metriche contenga almeno tutte le chiavi canoniche.
    Non impone vincoli sui tipi dei valori (per ora).

    Lancia ValueError se manca una chiave fondamentale.
    """
    missing: List[str] = [k for k in LMETRICS_METRIC_KEYS if k not in metrics]
    if missing:
        raise ValueError(
            "Bus di metriche incompleto: mancano le chiavi canoniche: "
            + ", ".join(missing)
        )


def make_witness_json(
    lm_id: str,
    metrics: Dict[str, Any],
    role: Optional[str] = None,
    source: str = "loventre_engine_clean_seed_v3",
    tags: Optional[Dict[str, Any]] = None,
    validate: bool = True,
) -> LMetricsWitnessJSON:
    """
    Costruisce un oggetto LMetricsWitnessJSON a partire da:
    - lm_id:   identificatore canonico del witness,
    - metrics: bus di metriche calcolato dal motore,
    - role:    ruolo logico (se None, usa COQ_WITNESS_ROLES se disponibile),
    - source:  descrizione della sorgente / versione del motore,
    - tags:    metadati opzionali aggiuntivi,
    - validate: se True, verifica che tutte le chiavi canoniche siano presenti.
    """
    if role is None:
        role = COQ_WITNESS_ROLES.get(lm_id, "unknown_role")

    if tags is None:
        tags = {}

    if validate:
        validate_metrics_bus(metrics)

    return LMetricsWitnessJSON(
        lm_id=lm_id,
        role=role,
        source=source,
        metrics=dict(metrics),
        tags=dict(tags),
    )


# ---------------------------------------------------------------------------
# 5. Serializzazione / deserializzazione su file JSON
# ---------------------------------------------------------------------------

def save_witness_json(witness: LMetricsWitnessJSON, path: Path) -> None:
    """
    Salva un witness LMetrics in un file JSON con indentazione leggibile.
    """
    data = witness.to_ordered_dict()
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)


def load_witness_json(path: Path, validate: bool = True) -> LMetricsWitnessJSON:
    """
    Carica un witness LMetrics da un file JSON e, opzionalmente, valida
    la presenza delle chiavi canoniche nel bus di metriche.
    """
    path = Path(path)
    with path.open("r", encoding="utf-8") as f:
        data = json.load(f)

    lm_id = str(data.get("lm_id", ""))
    role = str(data.get("role", "unknown_role"))
    source = str(data.get("source", "unknown_source"))
    metrics = dict(data.get("metrics", {}))
    tags = dict(data.get("tags", {}))

    if validate:
        validate_metrics_bus(metrics)

    return LMetricsWitnessJSON(
        lm_id=lm_id,
        role=role,
        source=source,
        metrics=metrics,
        tags=tags,
    )


# ---------------------------------------------------------------------------
# 6. Entry point minimale di debug (opzionale)
# ---------------------------------------------------------------------------

def _demo_dummy_witness() -> None:
    """
    Piccolo demo interno: costruisce un witness fittizio con metriche nulle
    e lo stampa su stdout in formato JSON. NON usato in produzione, solo per
    test manuali rapidi.
    """
    dummy_metrics: Dict[str, Any] = {k: None for k in LMETRICS_METRIC_KEYS}
    w = make_witness_json(
        lm_id="m_seed11_cli_demo",
        metrics=dummy_metrics,
        tags={"demo": True, "note": "dummy witness, valori None"},
        validate=False,
    )
    print(json.dumps(w.to_ordered_dict(), ensure_ascii=False, indent=2))


if __name__ == "__main__":
    # Se invochi questo modulo direttamente:
    #   python3 loventre_json_schema.py
    # vedrai un esempio di JSON per m_seed11_cli_demo con metriche None.
    _demo_dummy_witness()

