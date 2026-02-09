from pathlib import Path
import ast


def main() -> None:
    path = Path("loventre_meta_decision_engine.py")
    code = path.read_text(encoding="utf-8")

    # Idempotenza: se esiste già l'adapter Schwarzschild, non facciamo nulla.
    if "def append_schwarzschild_layer_to_metrics" in code:
        print("Patch già applicata; nessuna modifica necessaria.")
        return

    new_code = code

    # 1) Rimpiazziamo il blocco Schwarzschild inline nel tail di
    # meta_decide_instance_with_mass con una chiamata all'adapter.
    old_block = r"""    # Strato Schwarzschild-Loventre: compattezza e gamma da buco nero toy.
    try:
        from loventre_schwarzschild_lab import enrich_metrics_with_schwarzschild

        # Enrichment non distruttivo: aggiunge chi, regime e gamma_schwarzschild.
        metrics = enrich_metrics_with_schwarzschild(
            metrics,
            overwrite=False,
        )

        chi = float(metrics.get("schwarzschild_compactness", 0.0))
        reg_schw = str(metrics.get("schwarzschild_regime", "SUBCRITICAL"))
        gamma_schw = float(metrics.get("gamma_dilation_schwarzschild", 1.0))

        schw_snippet = (
            f"regime Schwarzschild-Loventre={reg_schw}, "
            f"compactness≈{chi:.3f}, gamma_schwarzschild≈{gamma_schw:.2f}"
        )

        base_expl = metrics.get("meta_explanation", "").rstrip()
        if base_expl:
            metrics["meta_explanation"] = (
                base_expl
                + "\n\n- Strato Schwarzschild-Loventre:\n  "
                + schw_snippet
            )
        else:
            metrics["meta_explanation"] = (
                "- Strato Schwarzschild-Loventre:\n  " + schw_snippet
            )
    except Exception:
        # Se qualcosa va storto (mancano massa, a_min, V0, ecc.), ignoriamo silenziosamente.
        pass

    metrics = append_planck_layer_to_metrics(metrics)
    return metrics
"""

    new_block = """    metrics = append_schwarzschild_layer_to_metrics(metrics)
    metrics = append_planck_layer_to_metrics(metrics)
    return metrics
"""

    if old_block not in new_code:
        print("Blocco Schwarzschild atteso non trovato; nessuna modifica effettuata.")
    else:
        new_code = new_code.replace(old_block, new_block)

    # 2) Inseriamo l'adapter Schwarzschild appena prima di append_hawking_layer_to_metrics.
    marker = "\n\ndef append_hawking_layer_to_metrics(metrics: dict) -> dict:\n"
    if marker not in new_code:
        print("Marker append_hawking_layer_to_metrics non trovato; non inserisco adapter Schwarzschild.")
    else:
        adapter = """
def append_schwarzschild_layer_to_metrics(metrics: dict) -> dict:
    \"\"\"Adapter di alto livello per lo strato Schwarzschild–Loventre.\"\"\"
    try:
        from loventre_schwarzschild_lab import enrich_metrics_with_schwarzschild
    except Exception:
        return metrics

    try:
        # Enrichment non distruttivo: aggiunge chi, regime e gamma_schwarzschild.
        metrics = enrich_metrics_with_schwarzschild(
            metrics,
            overwrite=False,
        )

        chi = float(metrics.get("schwarzschild_compactness", 0.0))
        reg_schw = str(metrics.get("schwarzschild_regime", "SUBCRITICAL"))
        gamma_schw = float(metrics.get("gamma_dilation_schwarzschild", 1.0))

        schw_snippet = (
            f"regime Schwarzschild-Loventre={reg_schw}, "
            f"compactness≈{chi:.3f}, gamma_schwarzschild≈{gamma_schw:.2f}"
        )

        base_expl = metrics.get("meta_explanation", "").rstrip()
        if base_expl:
            metrics["meta_explanation"] = (
                base_expl
                + \"\\n\\n- Strato Schwarzschild-Loventre:\\n  \"
                + schw_snippet
            )
        else:
            metrics["meta_explanation"] = (
                \"- Strato Schwarzschild-Loventre:\\n  \" + schw_snippet
            )
    except Exception:
        # Se qualcosa va storto (mancano massa, a_min, V0, ecc.), ignoriamo silenziosamente.
        return metrics

    return metrics

"""
        new_code = new_code.replace(marker, "\n\n" + adapter + marker.lstrip("\n"))

    # 3) Validazione sintattica
    try:
        ast.parse(new_code)
    except SyntaxError as exc:
        print("Errore di sintassi dopo la patch; non ho toccato il file.")
        print("Dettaglio:", exc)
        return

    path.write_text(new_code, encoding="utf-8")
    print("Patch meta_engine_cleanup_part2 applicata con successo. Sintassi OK.")


if __name__ == "__main__":
    main()

