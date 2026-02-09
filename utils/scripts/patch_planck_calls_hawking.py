from pathlib import Path
import ast
import sys

def main() -> None:
    path = Path("loventre_meta_decision_engine.py")
    if not path.exists():
        print("File loventre_meta_decision_engine.py non trovato.")
        sys.exit(1)

    code = path.read_text(encoding="utf-8")

    # Vogliamo intervenire SOLO sulla versione "finale" di append_planck_layer_to_metrics,
    # quella con la docstring "Versione finale: ...".
    marker_with_hawking = (
        'def append_planck_layer_to_metrics(metrics: dict) -> dict:\n'
        '    """Versione finale: applica il layer Planck–Loventre e aggiorna meta_explanation."""\n'
        '    metrics = append_hawking_layer_to_metrics(metrics)\n'
    )

    if marker_with_hawking in code:
        print("Planck layer già chiama Hawking; nessuna modifica necessaria.")
        return

    marker_plain = (
        'def append_planck_layer_to_metrics(metrics: dict) -> dict:\n'
        '    """Versione finale: applica il layer Planck–Loventre e aggiorna meta_explanation."""\n'
    )

    if marker_plain not in code:
        print("Definizione 'Versione finale' di append_planck_layer_to_metrics non trovata; nessuna modifica effettuata.")
        return

    new_code = code.replace(
        marker_plain,
        marker_with_hawking,
    )

    try:
        ast.parse(new_code)
    except SyntaxError as exc:
        print("Errore di sintassi dopo la patch; non ho toccato il file.")
        print("Dettaglio:", exc)
        return

    path.write_text(new_code, encoding="utf-8")
    print("✅ Patch applicata: append_planck_layer_to_metrics ora chiama anche append_hawking_layer_to_metrics.")

if __name__ == "__main__":
    main()

