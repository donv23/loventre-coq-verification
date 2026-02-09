from pathlib import Path
import re
import ast
import sys


def ensure_hawking_adapter(code: str) -> str:
    # Inserisce def append_hawking_layer_to_metrics se mancante.
    if "def append_hawking_layer_to_metrics" in code:
        return code

    adapter_block = """
def append_hawking_layer_to_metrics(metrics: dict) -> dict:
    \"\"\"Adapter di alto livello per lo strato Hawking–Loventre.\"\"\"
    try:
        from loventre_hawking_layer import compute_hawking_layer
    except Exception:
        return metrics

    try:
        return compute_hawking_layer(metrics)
    except Exception:
        return metrics

"""

    pattern = r"\ndef append_planck_layer_to_metrics\("
    if re.search(pattern, code):
        return re.sub(
            pattern,
            "\n" + adapter_block + "\ndef append_planck_layer_to_metrics(",
            code,
            count=1,
        )

    # Fallback: se non troviamo append_planck_layer_to_metrics, appende in fondo
    return code + "\n" + adapter_block


def ensure_hawking_hook_in_tail(code: str) -> str:
    # Inserisce la chiamata a append_hawking_layer_to_metrics prima di append_planck_layer_to_metrics.
    if "append_hawking_layer_to_metrics(metrics)" in code:
        return code

    pattern = r"(\n(?P<indent>\s*)metrics\s*=\s*append_planck_layer_to_metrics\(metrics\)\s*\n)"

    def repl(match: "re.Match") -> str:
        indent = match.group("indent")
        return (
            "\n"
            + indent
            + "metrics = append_hawking_layer_to_metrics(metrics)\n"
            + indent
            + "metrics = append_planck_layer_to_metrics(metrics)\n"
        )

    new_code, count = re.subn(pattern, repl, code, count=1)
    if count == 0:
        print(
            "Attenzione: non ho trovato la riga con append_planck_layer_to_metrics(metrics) nel tail; nessun hook Hawking inserito."
        )
        return code

    return new_code


def main() -> None:
    path = Path("loventre_meta_decision_engine.py")
    if not path.exists():
        print("File loventre_meta_decision_engine.py non trovato.")
        sys.exit(1)

    original_code = path.read_text(encoding="utf-8")

    new_code = ensure_hawking_adapter(original_code)
    new_code = ensure_hawking_hook_in_tail(new_code)

    if new_code == original_code:
        print(
            "Nessuna modifica necessaria (adapter e hook Hawking già presenti "
            "oppure pattern non trovato)."
        )
        return

    try:
        ast.parse(new_code)
    except SyntaxError as exc:
        print("Errore di sintassi dopo la patch; non ho toccato il file.")
        print("Dettaglio:", exc)
        return

    path.write_text(new_code, encoding="utf-8")
    print("Patch Hawking–Loventre applicata con successo. Sintassi OK.")


if __name__ == "__main__":
    main()

