#!/usr/bin/env python3
"""
Patch Loventre:

Aggiunge a loventre_meta_decision_engine.py un wrapper sicuro

    meta_decide_instance_with_mass_global

che chiama la funzione esistente
    meta_decide_instance_with_mass

e poi applica l'helper di livello engine
    loventre_attach_global_decision_to_metrics

per agganciare il blocco 'loventre_global' al metrics bus.

La patch è idempotente: se trova il marker
    # === LOVENTRE_MASS_DECISION_WITH_GLOBAL_WRAPPER ===
non fa nulla.
"""

from pathlib import Path


def main() -> None:
    path = Path("loventre_meta_decision_engine.py")
    if not path.exists():
        print("[Loventre] ERRORE: file loventre_meta_decision_engine.py non trovato.")
        return

    text = path.read_text(encoding="utf-8")
    marker = "# === LOVENTRE_MASS_DECISION_WITH_GLOBAL_WRAPPER ==="

    if marker in text:
        print(
            "[Loventre] Wrapper meta_decide_instance_with_mass_global già presente "
            "(marker trovato). Nessuna modifica necessaria."
        )
        return

    block = '''
# === LOVENTRE_MASS_DECISION_WITH_GLOBAL_WRAPPER ===
"""Wrapper Loventre di alto livello per meta_decide_instance_with_mass.

Non modifica la funzione originale, ma fornisce una variante che:
  1) chiama meta_decide_instance_with_mass(*args, **kwargs),
  2) cerca il metrics bus nel risultato,
  3) applica loventre_attach_global_decision_to_metrics,
  4) restituisce un dict con il blocco 'loventre_global' agganciato.

Pensato per l'uso in contesti in cui serve già una struttura Coq–friendly
(allineata al Loventre Metrics Bus + decisione globale).
"""

def meta_decide_instance_with_mass_global(*args, family: str = "generic", **kwargs):
    \"\"\"Versione 'globalizzata' di meta_decide_instance_with_mass.

    Parametri
    ----------
    *args, **kwargs :
        Passati direttamente a meta_decide_instance_with_mass (backward compat).

    family : str
        Etichetta della famiglia da passare a loventre_attach_global_decision_to_metrics
        (es. 'seed_grid', 'TSP_crit_n', 'SAT_crit_n', 'generic', ...).

    Ritorna
    -------
    dict
        Il risultato di meta_decide_instance_with_mass, eventualmente arricchito con
        il blocco 'loventre_global' sul metrics bus.
    \"\"\"
    # 1) Eseguiamo la logica originale
    result = meta_decide_instance_with_mass(*args, **kwargs)

    # 2) Se il risultato non è un dict, non possiamo arricchirlo in modo sensato
    if not isinstance(result, dict):
        return result

    # 3) Caso principale: il metrics bus è incapsulato sotto la chiave 'metrics'
    metrics_obj = result.get("metrics")
    if isinstance(metrics_obj, dict):
        enriched_metrics = loventre_attach_global_decision_to_metrics(
            metrics_obj, family=family
        )
        out = dict(result)
        out["metrics"] = enriched_metrics
        return out

    # 4) Caso alternativo: il risultato stesso assomiglia a un metrics bus
    keys = set(result.keys())
    bus_like_keys = {"kappa_eff", "entropy_eff", "V0", "p_tunnel", "gamma_dilation"}
    if keys & bus_like_keys:
        return loventre_attach_global_decision_to_metrics(result, family=family)

    # 5) Fallback: nessun arricchimento possibile in modo robusto
    return result
'''

    new_text = text.rstrip() + "\n\n" + block.lstrip() + "\n"
    path.write_text(new_text, encoding="utf-8")
    print(
        "[Loventre] Wrapper meta_decide_instance_with_mass_global aggiunto a "
        "loventre_meta_decision_engine.py."
    )


if __name__ == "__main__":
    main()

