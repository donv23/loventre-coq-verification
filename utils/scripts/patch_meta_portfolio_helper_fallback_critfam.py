from pathlib import Path
import re


MARKER_FALLBACK = "# === LOVENTRE_FALLBACK_GLOBAL_DECISION_CRITFAM ==="


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    target = root / "loventre_meta_portfolio_lab.py"

    if not target.exists():
        print(f"[Loventre] ERRORE: file non trovato: {target}")
        return

    src = target.read_text(encoding="utf-8")

    if MARKER_FALLBACK in src:
        print(
            "[Loventre] Helper loventre_attach_global_decision_to_family "
            "già aggiornato con fallback critico (marker trovato). "
            "Nessuna modifica necessaria."
        )
        return

    pattern = re.compile(
        r"def loventre_attach_global_decision_to_family\(records, family_name: str = \"TSP_crit_n\"\):"
        r"[\s\S]*?^\s*return enriched\n",
        re.MULTILINE,
    )

    patch_block = '''def loventre_attach_global_decision_to_family(records, family_name: str = "TSP_crit_n"):
    """Restituisce una nuova lista di record con campi global_decision/global_color/global_score.

    Parametri
    ----------
    records : iterabile di dict
        Ogni record è pensato come un "metrics bus" arricchito: kappa_eff, entropy_eff,
        V0, p_tunnel, gamma_dilation, risk_index, mass_eff, ecc. Possono esserci anche
        altri campi (region, difficulty_label, ecc.): vengono preservati.

    family_name : str
        Etichetta della famiglia (es. "TSP_crit_n", "SAT_crit_n", "seed_grid", ...).
    """  # noqa: E501
    # === LOVENTRE_FALLBACK_GLOBAL_DECISION_CRITFAM ===
    enriched = []

    for rec in records:
        # Copia difensiva per non mutare l'oggetto originale
        base = dict(rec)

        # Proviamo ad allinearci al Loventre Metrics Bus
        try:
            from loventre_metrics_bus import ensure_loventre_keys
            base_bus = ensure_loventre_keys(dict(base))
        except Exception:
            base_bus = dict(base)

        # Allineamento di alcuni alias (mass_eff/mass_mean, inerzia, gamma)
        mass_eff = base_bus.get("mass_eff", base_bus.get("mass_mean"))
        if mass_eff is not None:
            base_bus.setdefault("mass_eff", mass_eff)
            base_bus.setdefault("mass_mean", mass_eff)

        inertial_idx = base_bus.get(
            "inertial_idx", base_bus.get("inertial_difficulty_index")
        )
        if inertial_idx is not None:
            base_bus.setdefault("inertial_idx", inertial_idx)
            base_bus.setdefault("inertial_difficulty_index", inertial_idx)

        if "gamma_dilation" not in base_bus and "gamma_dil" in base_bus:
            base_bus["gamma_dilation"] = base_bus["gamma_dil"]

        gd = None

        # 1) Tentativo: usare la loventre_global_decision ufficiale
        try:
            gd = _loventre_global_decision_helper(base_bus, family=family_name)
        except TypeError:
            # Fallback nel caso la funzione non esponga il parametro 'family'
            try:
                gd = _loventre_global_decision_helper(base_bus)
            except Exception:
                gd = None
        except Exception:
            gd = None

        # 2) Se non abbiamo un dict valido, usiamo un fallback interno
        if not isinstance(gd, dict):
            p_s = float(
                base_bus.get("P_success", base_bus.get("p_success", base_bus.get("p_tunnel", 0.0))) or 0.0
            )
            gamma = float(
                base_bus.get("gamma_dilation", base_bus.get("gamma_dil", 1.0)) or 1.0
            )
            mass_eff_fb = float(
                base_bus.get("mass_eff", base_bus.get("mass_mean", 1.0)) or 1.0
            )
            inertial_idx_fb = float(
                base_bus.get(
                    "inertial_idx", base_bus.get("inertial_difficulty_index", 0.0)
                ) or 0.0
            )
            time_regime = str(base_bus.get("time_regime", "time_hyperbolic"))

            if time_regime == "time_euclidean":
                tr_penalty = 0.0
            elif time_regime == "time_threshold":
                tr_penalty = 1.0
            else:
                tr_penalty = 3.0

            # Proxy di rischio: tempo iperbolico, gamma alta, massa e inerzia pesanti
            risk_proxy = (
                tr_penalty
                + max(0.0, gamma - 1.0)
                + 0.3 * mass_eff_fb
                + 0.1 * (inertial_idx_fb / 10.0)
            )

            denom = 1.0 + 0.15 * risk_proxy
            global_score = p_s / denom
            if global_score < 0.0:
                global_score = 0.0
            if global_score > 1.0:
                global_score = 1.0

            if global_score >= 0.6:
                g_decision = "INSISTI"
                g_color = "GREEN"
            elif global_score >= 0.25:
                g_decision = "VALUTA"
                g_color = "AMBER"
            else:
                g_decision = "RITIRA"
                g_color = "RED"

            gd = {
                "global_decision": g_decision,
                "global_color": g_color,
                "global_score": global_score,
                "loventre_global_explanation": (
                    f"[fallback] Famiglia {family_name}: P_success ~ {p_s:.3e}, "
                    f"gamma_dilation ~ {gamma:.2f}, massa_eff ~ {mass_eff_fb:.2f}, "
                    f"indice_inerziale ~ {inertial_idx_fb:.2f}, time_regime={time_regime}. "
                    "Score globale calcolato come P_success penalizzato da massa, inerzia "
                    "e regime temporale critico."
                ),
            }

        # Se la funzione (o il fallback) restituisce un dict, estraiamo i campi canonici
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
'''

    new_src, n = pattern.subn(patch_block + "\n", src, count=1)

    if n == 0:
        print(
            "[Loventre] ATTENZIONE: non sono riuscito a trovare "
            "la definizione di loventre_attach_global_decision_to_family da patchare."
        )
        return

    target.write_text(new_src, encoding="utf-8")
    print(
        "[Loventre] Helper loventre_attach_global_decision_to_family "
        "aggiornato con fallback critico per famiglie TSP_crit_n / SAT_crit_n."
    )


if __name__ == "__main__":
    main()

