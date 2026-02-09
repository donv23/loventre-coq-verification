"""
loventre_mass_layer_v6.py

STEP 1 – MASS LAYER (annotativo, non causale)
Gennaio 2026 — Loventre Engine v6

Questo layer:
  - NON modifica kappa_eff
  - NON influenza la decisione
  - Annota due grandezze:
        mass_eff       → una “massa informazionale”
        inertial_idx   → indice di inerzia (resistenza al cambiamento)

Obiettivo:
  Portare un concetto fisico minimo senza alterare l'irreversibilità.
"""

from typing import Dict, Any


def compute_mass_layer(metrics: Dict[str, Any]) -> Dict[str, Any]:
    """
    Calcola la massa informazionale e l'indice di inerzia.
    Nessun campo critico viene modificato.
    Tutto viene aggiunto in modo NON invasivo.
    """

    # Seed protetti
    kappa = float(metrics.get("kappa_eff", 0.0) or 0.0)
    entropy = float(metrics.get("entropy_eff", 0.0) or 0.0)

    # Massa base:
    #   più entropia → più “peso”
    #   sicurezza totale se nessun input → 0.0
    mass_eff = abs(kappa) * (1.0 + max(entropy, 0.0))

    # Indice di inerzia:
    #   quanto "resiste" allo spostamento decisionale
    #   rimane completamente descrittivo
    inertial_idx = min(1.0, mass_eff / 10.0)

    # Annotazione NON intrusiva
    return {
        "mass_eff": mass_eff,
        "inertial_idx": inertial_idx,
        "mass_layer_active": True,
        "mass_layer_comment": (
            "STEP1 MASS v6 — annotazione non causale; "
            "nessuna influenza su decisione o kappa_eff"
        )
    }


def append_mass_layer_to_metrics(metrics: Dict[str, Any]) -> Dict[str, Any]:
    """
    Punto d’ingresso pulito e idempotente:
      - copia difensiva
      - aggiunge campi
      - non tocca altri layer
    """
    enriched = dict(metrics)
    mass_info = compute_mass_layer(enriched)
    enriched.update(mass_info)
    return enriched

