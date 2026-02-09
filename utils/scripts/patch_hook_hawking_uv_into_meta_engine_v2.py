#!/usr/bin/env python3
import ast
import pathlib
import sys


def find_meta_engine_file(root: pathlib.Path) -> pathlib.Path | None:
    candidates = list(root.rglob("loventre_meta_decision_engine.py"))
    if not candidates:
        print("[Loventre] Nessun loventre_meta_decision_engine.py trovato nel progetto.", file=sys.stderr)
        return None
    if len(candidates) > 1:
        print("[Loventre] ATTENZIONE: trovati più file loventre_meta_decision_engine.py:", file=sys.stderr)
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
    """
    if "append_hawking_uv_layer_to_metrics(metrics)" in text:
        # già collegato
        return None

    lines = text.splitlines(keepends=True)
    n = len(lines)

    # trova la definizione top-level
    def_idx = None
    for i, line in enumerate(lines):
        stripped = line.lstrip()
        if stripped.startswith("def append_hawking_layer_to_metrics(") and line == stripped:
            def_idx = i
            break

    if def_idx is None:
        print("[Loventre] WARNING: append_hawking_layer_to_metrics non trovata nel meta–engine.", file=sys.stderr)
        return None

    # cerca l'ULTIMO 'return metrics' dentro la funzione
    return_idx = None
    return_indent = None

    for i in range(def_idx + 1, n):
        line = lines[i]
        stripped = line.lstrip()

        # fine funzione: nuova def/class top-level
        if (line.startswith("def ") or line.startswith("class ")) and line == stripped:
            break

        if stripped.startswith("return metrics"):
            return_idx = i
            return_indent = line[: len(line) - len(stripped)]

    if return_idx is None or return_indent is None:
        print("[Loventre] WARNING: nessun 'return metrics' trovato in append_hawking_layer_to_metrics.", file=sys.stderr)
        return None

    uv_call_line = f"{return_indent}metrics = append_hawking_uv_layer_to_metrics(metrics)\n"

    # idempotenza extra
    if return_idx > 0 and lines[return_idx - 1] == uv_call_line:
        return None

    new_lines = lines[:return_idx] + [uv_call_line] + lines[return_idx:]
    return "".join(new_lines)


def ensure_import_for_uv(text: str) -> str:
    """
    Garantisce che esista un import per append_hawking_uv_layer_to_metrics.
    Prova prima ad aggiungerlo a una riga 'from ...loventre_hawking_layer import ...',
    altrimenti inserisce una nuova riga di import dopo il blocco import iniziale.
    """
    lines = text.splitlines(keepends=True)

    # se già c'è un import esplicito con il nome, non facciamo nulla
    for line in lines:
        if "append_hawking_uv_layer_to_metrics" in line and "import" in line:
            return text

    # prova ad estendere un import esistente da loventre_hawking_layer
    for i, line in enumerate(lines):
        if "import" in line and "loventre_hawking_layer" in line and "append_hawking_uv_layer_to_metrics" not in line:
            stripped = line.rstrip("\n")
            if " import " in stripped:
                new_line = stripped + ", append_hawking_uv_layer_to_metrics\n"
                lines[i] = new_line
                return "".join(lines)

    # altrimenti, inserisce un nuovo import dopo il blocco iniziale di import/commenti
    insert_at = 0
    for i, line in enumerate(lines):
        stripped = line.lstrip()
        if stripped.startswith("import ") or stripped.startswith("from "):
            insert_at = i + 1
            continue
        if stripped.startswith("#") or stripped == "":
            if insert_at == i:
                insert_at = i + 1
            continue
        break

    import_line = "from loventre_hawking_layer import append_hawking_uv_layer_to_metrics\n"
    new_lines = lines[:insert_at] + [import_line] + lines[insert_at:]
    return "".join(new_lines)


def main():
    root = pathlib.Path(__file__).resolve().parents[1]
    target = find_meta_engine_file(root)
    if target is None:
        return

    print(f"[Loventre] Target meta–engine: {target}")

    original_text = target.read_text(encoding="utf-8")

    new_text = hook_uv_call_into_append_function(original_text)
    if new_text is None:
        print("[Loventre] Nessuna modifica necessaria (call UV già presente o funzione assente).")
        return

    new_text = ensure_import_for_uv(new_text)

    # verifica sintattica
    try:
        ast.parse(new_text, filename=str(target))
    except SyntaxError as e:
        print("[Loventre] ERRORE: la patch hook UV romperebbe la sintassi, annullo.", file=sys.stderr)
        print(e, file=sys.stderr)
        return

    target.write_text(new_text, encoding="utf-8")
    print("[Loventre] Hawking UV agganciato a append_hawking_layer_to_metrics nel meta–engine.")


if __name__ == "__main__":
    main()

