from pathlib import Path
import re
import ast
import sys


def main() -> None:
    path = Path("loventre_meta_decision_engine.py")
    if not path.exists():
        print("File loventre_meta_decision_engine.py non trovato.")
        sys.exit(1)

    code = path.read_text(encoding="utf-8")

    # Se il hook Hawking è già presente, non fare nulla
    if "metrics = append_hawking_layer_to_metrics(metrics)" in code:
        print("Hook Hawking già presente, nessuna modifica necessaria.")
        return

    # Cerchiamo la riga con append_schwarzschild_layer_to_metrics e inseriamo Hawking subito dopo.
    pattern = r"(\n(?P<indent>\s*)metrics\s*=\s*append_schwarzschild_layer_to_metrics\(metrics\)\s*\n)"

    def repl(match: "re.Match") -> str:
        indent = match.group("indent")
        return (
            "\n"
            + indent
            + "metrics = append_schwarzschild_layer_to_metrics(metrics)\n"
            + indent
            + "metrics = append_hawking_layer_to_metrics(metrics)\n"
        )

    new_code, count = re.subn(pattern, repl, code, count=1)

    if count == 0:
        print(
            "Pattern con append_schwarzschild_layer_to_metrics(metrics) non trovato; "
            "nessuna modifica effettuata."
        )
        return

    try:
        ast.parse(new_code)
    except SyntaxError as exc:
        print("Errore di sintassi dopo la patch Hawking tail; non ho toccato il file.")
        print("Dettaglio:", exc)
        return

    path.write_text(new_code, encoding="utf-8")
    print("Hook Hawking inserito con successo dopo lo strato Schwarzschild.")


if __name__ == "__main__":
    main()

