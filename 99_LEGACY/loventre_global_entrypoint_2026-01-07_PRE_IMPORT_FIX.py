"""
loventre_global_entrypoint.py

Entry point globale “ufficiale” del Loventre Engine Python (stato: dicembre 2025).

Questo modulo fornisce una funzione stabile:

    loventre_global_decide_with_policy(**kwargs) -> dict

che:
  1. chiama il motore globale meta_decide_instance_with_mass_global(...)
     (layer Einstein–Loventre, massa, Schwarzschild–Loventre, Planck–Loventre, ecc.),
  2. arricchisce le metriche con il Policy Bridge
     (global_decision_label, global_decision_score, global_meta_explanation),
  3. restituisce un dict `metrics` compatibile con il Loventre Metrics Bus
     e pronto per essere proiettato verso LMetrics/Coq.

La semantica globale è descritta nel seed:

    LOVENTRE_ENGINE_PYTHON_GLOBAL_STATE_SEED_2025-12.md
"""

from __future__ import annotations

from typing import Any, Dict

try:
    # Motore globale (layer fisici + global decision INSISTI/VALUTA/RITIRA)
    from loventre_meta_decision_engine import meta_decide_instance_with_mass_global
except ImportError as exc:  # pragma: no cover - messaggio chiaro per debug
    raise ImportError(
        "[Loventre] Impossibile importare meta_decide_instance_with_mass_global "
        "da loventre_meta_decision_engine. Verifica che il file esista e sia nel PYTHONPATH."
    ) from exc

try:
    # Policy Bridge qualitativo (safe/borderline/critical/invalid + spiegazione)
    from loventre_policy_bridge import apply_policy_bridge_to_metrics
except ImportError as exc:  # pragma: no cover
    raise ImportError(
        "[Loventre] Impossibile importare apply_policy_bridge_to_metrics "
        "da loventre_policy_bridge. Verifica che il file esista e sia nel PYTHONPATH."
    ) from exc


def loventre_global_decide_with_policy(**kwargs: Any) -> Dict[str, Any]:
    """
    Entry point globale stabile del Loventre Engine.

    Parametri
    ---------
    **kwargs :
        Vengono passati tali e quali alla funzione
        meta_decide_instance_with_mass_global(...).

        Questo permette di non vincolare qui la firma esatta;
        la semantica degli argomenti resta definita dal motore
        (loventre_meta_decision_engine.py) e dai seed concettuali.

    Ritorno
    -------
    metrics : dict
        Dizionario di metriche Loventre (Loventre Metrics Bus), arricchito con:
          - campo 'loventre_global' (global_decision, global_color, global_score)
          - campi del Policy Bridge:
              * global_decision_label  (safe/borderline/critical/invalid)
              * global_decision_score  (float in [0,1])
              * global_meta_explanation (stringa breve)

    Note
    ----
    Questo è il punto di ingresso da usare per:
      - altre librerie Python,
      - wrapper CLI/JSON,
      - ponte programmatico verso la pipeline LMetrics/Coq.

    Qualsiasi cambiamento importante alla semantica di questo entry point
    va riflesso nel seed:

      LOVENTRE_ENGINE_PYTHON_GLOBAL_STATE_SEED_2025-12.md
    """
    # 1. Esegui il motore globale (fisica + global decision numerica)
    metrics = meta_decide_instance_with_mass_global(**kwargs)

    if not isinstance(metrics, dict):
        raise TypeError(
            "[Loventre] meta_decide_instance_with_mass_global ha restituito "
            f"un oggetto di tipo {type(metrics)!r}, ma ci si aspettava un dict."
        )

    # 2. Applica il Policy Bridge per arricchire le metriche
    metrics_with_policy = apply_policy_bridge_to_metrics(metrics)

    if not isinstance(metrics_with_policy, dict):
        raise TypeError(
            "[Loventre] apply_policy_bridge_to_metrics ha restituito "
            f"un oggetto di tipo {type(metrics_with_policy)!r}, ma ci si aspettava un dict."
        )

    return metrics_with_policy


def loventre_global_entry(**kwargs: Any) -> Dict[str, Any]:
    """
    Alias di compatibilità per loventre_global_decide_with_policy.

    Da usare se si vuole un nome più breve; la semantica resta identica:
    motore globale + Policy Bridge -> metrics (dict).
    """
    return loventre_global_decide_with_policy(**kwargs)

