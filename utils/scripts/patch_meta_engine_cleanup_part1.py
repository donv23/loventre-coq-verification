from pathlib import Path
import ast


def main() -> None:
    path = Path("loventre_meta_decision_engine.py")
    code = path.read_text(encoding="utf-8")

    # Idempotenza: se vediamo il nuovo nome, la patch è già stata applicata.
    if "meta_decide_instance_with_mass_mass_layer_only" in code:
        print("Patch già applicata; nessuna modifica necessaria.")
        return

    new_code = code

    # 1) Rinominare la prima meta_decide_instance_with_mass (solo layer di massa + snippet).
    new_code = new_code.replace(
        "def meta_decide_instance_with_mass(history, E, V0_quantile=0.85, p_target=0.1, **kwargs):",
        "def _meta_decide_instance_with_mass_mass_layer_only(history, E, V0_quantile=0.85, p_target=0.1, **kwargs):",
    )

    # 2) Rinominare la prima append_planck_layer_to_metrics (quella con n_budget e planck_summary).
    new_code = new_code.replace(
        "def append_planck_layer_to_metrics(metrics: dict, n_budget: int | None = None) -> dict:",
        "def _append_planck_layer_to_metrics_with_summary_legacy(metrics: dict, n_budget: int | None = None) -> dict:",
    )

    # 3) Rinominare la prima apply_policy_bridge_to_metrics (versione legacy con policy_bridge_*).
    old_apply = '''def apply_policy_bridge_to_metrics(metrics: dict) -> dict:
    """Applica il Loventre Policy Bridge usando rischio, curvatura globale, compattezza e gamma Schwarzschild."""
'''
    new_apply = '''def _apply_policy_bridge_to_metrics_legacy(metrics: dict) -> dict:
    """[LEGACY] Applica il Loventre Policy Bridge usando rischio, curvatura globale, compattezza e gamma Schwarzschild."""
'''
    if old_apply in new_code:
        new_code = new_code.replace(old_apply, new_apply)

    # 4) Rinominare la prima append_policy_bridge_to_metrics (versione legacy che fa il blocco [Policy Bridge] ...).
    old_append = '''def append_policy_bridge_to_metrics(metrics: dict) -> dict:
    """Integra il Loventre Policy Bridge nelle metrics.
'''
    new_append = '''def _append_policy_bridge_to_metrics_inline_legacy(metrics: dict) -> dict:
    """[LEGACY] Integra il Loventre Policy Bridge nelle metrics.
'''
    if old_append in new_code:
        new_code = new_code.replace(old_append, new_append)

    # 5) Validazione sintattica
    try:
        ast.parse(new_code)
    except SyntaxError as exc:
        print("Errore di sintassi dopo la patch; non ho toccato il file.")
        print("Dettaglio:", exc)
        return

    path.write_text(new_code, encoding="utf-8")
    print("Patch meta_engine_cleanup_part1 applicata con successo. Sintassi OK.")


if __name__ == "__main__":
    main()

