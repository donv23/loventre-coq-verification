from pathlib import Path
import ast


def main() -> None:
    path = Path("loventre_meta_decision_engine.py")
    code = path.read_text(encoding="utf-8")

    # Idempotenza: se la coda chiama già apply_policy_bridge_to_metrics, non facciamo nulla.
    if "metrics = apply_policy_bridge_to_metrics(metrics)" in code:
        print("Patch già applicata; nessuna modifica necessaria.")
        return

    new_code = code

    # Tail attuale (dopo risk_profile) della meta_decide_instance_with_mass canonica.
    old_tail = (
        "    metrics = append_schwarzschild_layer_to_metrics(metrics)\n"
        "    metrics = append_planck_layer_to_metrics(metrics)\n"
        "    return metrics\n"
    )

    # Tail canonico con Policy Bridge integrato.
    new_tail = (
        "    metrics = append_schwarzschild_layer_to_metrics(metrics)\n"
        "    metrics = append_planck_layer_to_metrics(metrics)\n"
        "    metrics = apply_policy_bridge_to_metrics(metrics)\n"
        "    metrics = append_policy_bridge_to_metrics(metrics)\n"
        "    return metrics\n"
    )

    if old_tail not in new_code:
        print("Tail atteso non trovato; nessuna modifica effettuata.")
    else:
        new_code = new_code.replace(old_tail, new_tail)

    # Validazione sintassi
    try:
        ast.parse(new_code)
    except SyntaxError as exc:
        print("Errore di sintassi dopo la patch; non ho toccato il file.")
        print("Dettaglio:", exc)
        return

    path.write_text(new_code, encoding="utf-8")
    print("Patch meta_engine_policy_bridge_tail applicata con successo. Sintassi OK.")


if __name__ == "__main__":
    main()

