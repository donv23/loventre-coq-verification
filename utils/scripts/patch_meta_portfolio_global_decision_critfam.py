from pathlib import Path


MARKER = "# === LOVENTRE_PATCH_GLOBAL_DECISION_CRITFAM ==="


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    target = root / "loventre_meta_portfolio_lab.py"

    if not target.exists():
        print(f"[Loventre] ERRORE: file non trovato: {target}")
        return

    src = target.read_text(encoding="utf-8")

    if MARKER in src:
        print(
            "[Loventre] loventre_meta_portfolio_lab.py "
            "già aggiornato con helper per global_decision sulle famiglie critiche "
            "(marker trovato). Nessuna modifica necessaria."
        )
        return

    patch_block = (
        "\n\n"
        + MARKER
        + """
\"\"\"Helper Loventre per aggiungere global_decision/global_color/global_score
alle famiglie critiche (TSP_crit_n, SAT_crit_n, ecc.).

Questo blocco è stato aggiunto da
scripts/patch_meta_portfolio_global_decision_critfam.py (patch idempotente).
\"\"\"\n
from loventre_meta_decision_engine import loventre_global_decision


def loventre_attach_global_decision_to_family(records, family_name: str = "TSP_crit_n"):
    \"\"\"Restituisce una nuova lista di record con campi global_decision/global_color/global_score.

    Parametri
    ----------
    records : iterabile di dict
        Ogni record è pensato come un \"metrics bus\" arricchito: kappa_eff, entropy_eff,
        V0, p_tunnel, gamma_dilation, risk_index, mass_eff, ecc. Possono esserci anche
        altri campi (region, difficulty_label, ecc.): vengono preservati.

    family_name : str
        Etichetta della famiglia (es. "TSP_crit_n", "SAT_crit_n", "seed_grid", ...).
    \"\"\"  # noqa: E501
    enriched = []

    for rec in records:
        # Copia difensiva per non mutare l'oggetto originale
        base = dict(rec)

        # Chiamiamo loventre_global_decision cercando di rispettare la firma attuale.
        try:
            gd = loventre_global_decision(base, family=family_name)
        except TypeError:
            # Fallback nel caso la funzione non esponga il parametro 'family'
            gd = loventre_global_decision(base)

        # Se la funzione restituisce un dict, estraiamo i campi canonici
        if isinstance(gd, dict):
            base.setdefault("loventre_global", {})
            base["loventre_global"].update(
                {
                    "global_decision": gd.get("global_decision"),
                    "global_color": gd.get("global_color"),
                    "global_score": gd.get("global_score"),
                    "loventre_global_explanation": gd.get(
                        "loventre_global_explanation"
                    ),
                }
            )

        enriched.append(base)

    return enriched
"""
    )

    new_src = src + patch_block
    target.write_text(new_src, encoding="utf-8")

    print(
        "[Loventre] loventre_meta_portfolio_lab.py aggiornato con helper "
        "loventre_attach_global_decision_to_family (famiglie critiche)."
    )


if __name__ == "__main__":
    main()

