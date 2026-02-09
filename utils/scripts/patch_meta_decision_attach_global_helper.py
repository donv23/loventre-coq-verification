#!/usr/bin/env python3
"""
Patch Loventre:

Aggiunge a loventre_meta_decision_engine.py il helper di livello engine
    loventre_attach_global_decision_to_metrics

che prende un singolo metrics bus (dict) e gli aggancia il blocco
loventre_global (global_decision, global_color, global_score, spiegazione).

La patch è idempotente: se trova il marker
    # === LOVENTRE_ATTACH_GLOBAL_DECISION_TO_METRICS ===
non fa nulla.
"""

from pathlib import Path


def main() -> None:
    path = Path("loventre_meta_decision_engine.py")
    if not path.exists():
        print("[Loventre] ERRORE: file loventre_meta_decision_engine.py non trovato.")
        return

    text = path.read_text(encoding="utf-8")
    marker = "# === LOVENTRE_ATTACH_GLOBAL_DECISION_TO_METRICS ==="

    if marker in text:
        print(
            "[Loventre] Helper loventre_attach_global_decision_to_metrics già presente "
            "(marker trovato). Nessuna modifica necessaria."
        )
        return

    block = '''
# === LOVENTRE_ATTACH_GLOBAL_DECISION_TO_METRICS ===
"""Helper Loventre per agganciare la decisione globale ad un singolo metrics bus.

Questo helper è di livello engine: dato un dict di metriche (già vicino al Loventre
Metrics Bus) calcola global_decision / global_color / global_score e li inserisce
in un sotto–campo 'loventre_global', senza mutare l'oggetto originale.

Pensato per essere usato in:
  - analyze_instance / meta_analyze_instance,
  - meta_decide_instance,
  - meta_decide_instance_with_mass,
  - altri lab che operano su un singolo metrics bus.
"""

def loventre_attach_global_decision_to_metrics(m: dict, family: str = "generic") -> dict:
    """Ritorna una copia di ``m`` con il blocco ``loventre_global`` popolato.

    Parametri
    ----------
    m : dict
        Bus delle metriche Loventre (kappa_eff, entropy_eff, V0, p_tunnel,
        gamma_dilation, risk_index, mass_eff, ecc.). Possono esserci altri
        campi: vengono preservati.

    family : str
        Etichetta della famiglia (es. 'seed_grid', 'TSP_crit_n', 'SAT_crit_n',
        'generic', ...), passata a ``loventre_global_decision`` quando possibile.
    """
    # Copia difensiva per non mutare ``m``
    base = dict(m)

    # Allineamento facoltativo al Loventre Metrics Bus
    try:
        from loventre_metrics_bus import ensure_loventre_keys  # import locale per evitare cicli
        base_bus = ensure_loventre_keys(dict(base))
    except Exception:
        base_bus = dict(base)

    # Calcolo della decisione globale
    try:
        gd = loventre_global_decision(base_bus, family=family)
    except TypeError:
        # Fallback nel caso la firma non esponga ancora il parametro ``family``
        gd = loventre_global_decision(base_bus)

    if isinstance(gd, dict):
        # Unifichiamo eventuali campi preesistenti
        lg = dict(base.get("loventre_global", {}))
        lg.update(
            {
                "global_decision": gd.get("global_decision"),
                "global_color": gd.get("global_color"),
                "global_score": gd.get("global_score"),
                "loventre_global_explanation": gd.get("loventre_global_explanation"),
            }
        )
        base["loventre_global"] = lg

    return base
'''

    new_text = text.rstrip() + "\n\n" + block.lstrip() + "\n"
    path.write_text(new_text, encoding="utf-8")
    print(
        "[Loventre] Helper loventre_attach_global_decision_to_metrics aggiunto a "
        "loventre_meta_decision_engine.py."
    )


if __name__ == "__main__":
    main()

