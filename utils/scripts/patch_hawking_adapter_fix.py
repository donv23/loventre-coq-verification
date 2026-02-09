from pathlib import Path
import re
import ast
import sys

def main() -> None:
    path = Path("loventre_meta_decision_engine.py")
    if not path.exists():
        print("File principale non trovato.")
        sys.exit(1)

    code = path.read_text(encoding="utf-8")

    # Se l'adapter usa già enrich_metrics_with_hawking_layer, nessuna azione
    if "enrich_metrics_with_hawking_layer" in code:
        print("Adapter Hawking già corretto (usa enrich_metrics_with_hawking_layer).")
        return

    pattern = r"from loventre_hawking_layer import compute_hawking_layer"
    if pattern not in code:
        print("Pattern 'compute_hawking_layer' non trovato; nessuna modifica effettuata.")
        return

    new_code = code.replace(
        "from loventre_hawking_layer import compute_hawking_layer",
        "from loventre_hawking_layer import enrich_metrics_with_hawking_layer as compute_hawking_layer",
    )

    try:
        ast.parse(new_code)
    except SyntaxError as e:
        print("Errore di sintassi dopo la patch; non ho toccato il file.")
        print("Dettaglio:", e)
        return

    path.write_text(new_code, encoding="utf-8")
    print("✅ Adapter Hawking–Loventre corretto: ora importa enrich_metrics_with_hawking_layer.")
    

if __name__ == "__main__":
    main()

