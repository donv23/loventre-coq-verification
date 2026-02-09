"""
loventre_informational_enrich_v5.py

Versione: v5.2 (09 dicembre 2025)

Ruolo:
  - Fornire una funzione di "enrichment" delle metriche Loventre
    con un potenziale informazionale toy e la corrispondente
    classificazione SAFE / TRANSITIONAL / BLACKHOLE.
  - NON modifica JSON su disco, non tocca il core del motore:
    lavora solo su dizionari in memoria.

API principale:
  - enrich_metrics_with_toy_info(metrics) -> dict

Campi aggiunti nel dict risultante:
  - "informational_potential"    : float (toy)
  - "informational_regime_toy"   : str  ("SAFE"/"TRANSITIONAL"/"BLACKHOLE")
"""

from __future__ import annotations

from typing import Mapping, Any, Dict

from loventre_informational_order_v5 import (
    classify_informational_regime,
)
from loventre_informational_potential_toy_v5 import (
    compute_toy_informational_potential,
)


def enrich_metrics_with_toy_info(
    metrics: Mapping[str, Any],
) -> Dict[str, Any]:
    """
    Restituisce una copia del dict `metrics` arricchita con:

      - informational_potential : float (valore toy)
      - informational_regime_toy : str (SAFE / TRANSITIONAL / BLACKHOLE)

    Note:
      - Non modifica l'oggetto originale: crea una copia.
      - Usa la stessa logica di classificazione di
        loventre_informational_order_v5.classify_informational_regime.
    """
    toy_info = compute_toy_informational_potential(metrics)

    enriched = dict(metrics)
    enriched["informational_potential"] = toy_info

    # Per classificare il regime toy, usiamo il dict arricchito
    # (così la funzione di classificazione vede il nuovo campo).
    regime_toy = classify_informational_regime(enriched)
    enriched["informational_regime_toy"] = regime_toy

    return enriched


def _self_test() -> None:
    """
    Self-test minimale: arricchisce due casi sintetici SAFE-like / BH-like.
    """
    m_safe = {
        "kappa_eff": 0.3,
        "entropy_eff": 0.2,
        "V0": 0.1,
        "p_tunnel": 0.5,
        "P_success": 0.95,
    }

    m_bh = {
        "kappa_eff": 1.0,
        "entropy_eff": 0.8,
        "V0": 0.6,
        "p_tunnel": 0.05,
        "P_success": 0.1,
    }

    e_safe = enrich_metrics_with_toy_info(m_safe)
    e_bh = enrich_metrics_with_toy_info(m_bh)

    print("[SELF-TEST] SAFE-like:")
    print(f"  informational_potential   = {e_safe['informational_potential']:.3f}")
    print(f"  informational_regime_toy  = {e_safe['informational_regime_toy']}")
    print("[SELF-TEST] BH-like:")
    print(f"  informational_potential   = {e_bh['informational_potential']:.3f}")
    print(f"  informational_regime_toy  = {e_bh['informational_regime_toy']}")
    print("[loventre_informational_enrich_v5] self-test OK.")


if __name__ == "__main__":
    _self_test()

