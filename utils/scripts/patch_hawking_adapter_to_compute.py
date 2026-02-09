from pathlib import Path
import ast
import sys

def main() -> None:
    path = Path("loventre_meta_decision_engine.py")
    if not path.exists():
        print("File loventre_meta_decision_engine.py non trovato.")
        sys.exit(1)

    code = path.read_text(encoding="utf-8")

    # Cerchiamo e sostituiamo SOLO la parte di import sbagliata,
    # senza preoccuparci dell'indentazione (niente spazi all'inizio).
    old_snippet = "from loventre_hawking_layer import enrich_metrics_with_hawking_layer as compute_hawking_layer"
    new_snippet = "from loventre_hawking_layer import compute_hawking_layer"

    if new_snippet in code and old_snippet not in code:
        print("Adapter Hawking sembra già usare compute_hawking_layer; nessuna modifica necessaria.")
        return

    if old_snippet not in code:
        print("Snippet con enrich_metrics_with_hawking_layer non trovato; nessuna modifica effettuata.")
        return

    new_code = code.replace(old_snippet, new_snippet)

    try:
        ast.parse(new_code)
    except SyntaxError as exc:
        print("Errore di sintassi dopo la patch; non ho toccato il file.")
        print("Dettaglio:", exc)
        return

    path.write_text(new_code, encoding="utf-8")
    print("✅ Adapter Hawking–Loventre corretto: ora importa compute_hawking_layer come entry point.")

if __name__ == "__main__":
    main()

