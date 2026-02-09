#!/usr/bin/env python3
import ast
import pathlib
import sys


def find_hawking_layer_file(root: pathlib.Path) -> pathlib.Path | None:
    candidates = list(root.rglob("loventre_hawking_layer.py"))
    if not candidates:
        print("[Loventre] Nessun loventre_hawking_layer.py trovato nel progetto.", file=sys.stderr)
        return None
    if len(candidates) > 1:
        print("[Loventre] ATTENZIONE: trovati più file loventre_hawking_layer.py:", file=sys.stderr)
        for c in candidates:
            print("  -", c, file=sys.stderr)
        print("[Loventre] Per sicurezza non modifico niente. Specificare il file corretto.", file=sys.stderr)
        return None
    return candidates[0]


def hook_uv_call_into_append_function(text: str) -> str | None:
    """
    Inserisce, se non già presente, la chiamata:

        metrics = append_hawking_uv_layer_to_metrics(metrics)

    all'interno della funzione top-level:

        def append_hawking_layer_to_metrics(...):

    subito prima del 'return metrics' finale.
    Restituisce il nuovo sorgente, oppure None se nessuna modifica è necessaria
    (per idempotenza).
    """
    if "append_hawking_uv_layer_to_metrics(metrics)" in text:
        # già collegato
        return None

    lines = text.splitlines(keepends=True)
    n = len(lines)

    # trova la definizione top-level di append_hawking_layer_to_metrics
    def_idx = None
    for i, line in enumerate(lines):
        stripped = line.lstrip()
        if stripped.startswith("def append_hawking_layer_to_metrics(") and line == stripped:
            def_idx = i
            break

    if def_idx is None:
        print("[Loventre] WARNING: append_hawking_layer_to_metrics non trovata.", file=sys.stderr)
        return None

    # cerca un 'return metrics' dentro la funzione, per inserirci sopra la chiamata UV
    return_idx = None
    return_indent = None

    for i in range(def_idx + 1, n):
        line = lines[i]
        stripped = line.lstrip()

        # fine della funzione: nuova def/class top-level non vuota
        if (line.startswith("def ") or line.startswith("class ")) and line == stripped:
            break

        if stripped.startswith("return metrics"):
            return_idx = i
            return_indent = line[: len(line) - len(stripped)]
            # non facciamo break qui: teniamo l'ULTIMO return metrics
            # in caso ce ne siano più di uno
    if return_idx is None or return_indent is None:
        print("[Loventre] WARNING: nessun 'return metrics' trovato in append_hawking_layer_to_metrics.", file=sys.stderr)
        return None

    uv_call_line = f"{return_indent}metrics = append_hawking_uv_layer_to_metrics(metrics)\n"

    # se la riga precedente è già esattamente la chiamata UV, non facciamo nulla (idempotenza aggiuntiva)
    if return_idx > 0 and lines[return_idx - 1] == uv_call_line:
        return None

    # inserisce la chiamata UV immediatamente sopra il return
    new_lines = lines[:return_idx] + [uv_call_line] + lines[return_idx:]
    return "".join(new_lines)


def main():
    root = pathlib.Path(__file__).resolve().parents[1]
    target = find_hawking_layer_file(root)
    if target is None:
        return

    print(f"[Loventre] Target Hawking layer: {target}")

    original_text = target.read_text(encoding="utf-8")
    new_text = hook_uv_call_into_append_function(original_text)

    if new_text is None:
        print("[Loventre] Nessuna modifica necessaria (call UV già presente o funzione non trovata).")
        return

    # Verifica sintattica prima di scrivere
    try:
        ast.parse(new_text, filename=str(target))
    except SyntaxError as e:
        print("[Loventre] ERRORE: la patch hook UV romperebbe la sintassi, annullo.", file=sys.stderr)
        print(e, file=sys.stderr)
        return

    target.write_text(new_text, encoding="utf-8")
    print(f"[Loventre] Chiamata append_hawking_uv_layer_to_metrics(metrics) collegata alla pipeline Hawking.")


if __name__ == "__main__":
    main()

