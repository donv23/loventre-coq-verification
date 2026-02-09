#!/usr/bin/env python3
import ast
import pathlib
import sys

LEGACY_HELPERS = [
    "_append_planck_layer_to_metrics_with_summary_legacy",
    "_apply_policy_bridge_to_metrics_legacy",
    "_print_policy_bridge_section",
]


def drop_legacy_helper_block(lines, func_name):
    """
    Rimuove in modo conservativo un blocco di funzione top-level:

    def func_name(...):
        ...

    - Cerca solo definizioni NON indentate (colonna 0)
    - Include eventuali righe vuote prima e dopo il blocco
    - È idempotente: se la funzione non c'è, non modifica nulla
    """
    n = len(lines)
    idx = None

    for i, line in enumerate(lines):
        stripped = line.lstrip()
        if stripped.startswith(f"def {func_name}(") and line == stripped:
            idx = i
            break

    if idx is None:
        return lines, False

    # ingloba eventuali righe vuote precedenti
    start = idx
    while start > 0 and lines[start - 1].strip() == "":
        start -= 1

    # corpo: tutte le righe indentate finché non incontriamo un nuovo top-level
    end = idx + 1
    while end < n:
        line = lines[end]
        if line.startswith("def ") or line.startswith("class "):
            break
        if line.strip() != "" and not (line.startswith(" ") or line.startswith("\t")):
            break
        end += 1

    # ingloba eventuali righe vuote successive
    while end < n and lines[end].strip() == "":
        end += 1

    new_lines = lines[:start] + lines[end:]
    return new_lines, True


def find_meta_engine_file(root: pathlib.Path) -> pathlib.Path | None:
    """
    Cerca loventre_meta_decision_engine.py ovunque sotto root.
    Se ne trova uno solo, lo usa; se nessuno, restituisce None.
    Se più di uno, stampa un warning e restituisce None per sicurezza.
    """
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


def main():
    root = pathlib.Path(__file__).resolve().parents[1]
    target = find_meta_engine_file(root)

    if target is None:
        return

    print(f"[Loventre] Target meta–engine: {target}")

    if not target.exists():
        print(f"[Loventre] WARNING: file non trovato: {target}", file=sys.stderr)
        return

    original_text = target.read_text(encoding="utf-8")
    lines = original_text.splitlines(keepends=True)

    changed = False
    for name in LEGACY_HELPERS:
        lines, removed = drop_legacy_helper_block(lines, name)
        if removed:
            changed = True
            print(f"[Loventre] rimosso helper legacy: {name}")
        else:
            print(f"[Loventre] nessuna definizione top-level trovata per: {name}")

    if not changed:
        print("[Loventre] nessuna modifica necessaria (helpers già assenti).")
        return

    new_text = "".join(lines)

    try:
        ast.parse(new_text, filename=str(target))
    except SyntaxError as e:
        print("[Loventre] ERRORE: la patch romperebbe la sintassi, annullo.", file=sys.stderr)
        print(e, file=sys.stderr)
        return

    target.write_text(new_text, encoding="utf-8")
    print(f"[Loventre] Patch applicata con successo a {target}")


if __name__ == "__main__":
    main()

