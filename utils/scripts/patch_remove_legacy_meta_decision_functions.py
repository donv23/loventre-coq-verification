#!/usr/bin/env python3
"""
Patch: rimuove due funzioni legacy da loventre_meta_decision_engine.py
solo se non risultano usate in nessun altro file Python del progetto.

Target:
- _append_policy_bridge_to_metrics_inline_legacy
- _meta_decide_instance_with_mass_mass_layer_only

Idempotente: se le funzioni sono già rimosse, non fa danni.
"""

import ast
import re
from pathlib import Path
from typing import List


LEGACY_FUNCTIONS = [
    "_append_policy_bridge_to_metrics_inline_legacy",
    "_meta_decide_instance_with_mass_mass_layer_only",
]


def find_usages(root: Path, func_name: str) -> List[Path]:
    """Cerca utilizzi del simbolo func_name in tutti i .py sotto root,
    escluso loventre_meta_decision_engine.py.
    Conta sia ast.Name che ast.Attribute.attr.
    """
    usages: List[Path] = []

    for path in root.rglob("*.py"):
        # escludiamo il file stesso dove andremo a patchare
        if path.name == "loventre_meta_decision_engine.py":
            continue

        try:
            src = path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue

        try:
            tree = ast.parse(src, filename=str(path))
        except SyntaxError:
            # file non ben formati o esperimenti vecchi: ignoriamo
            continue

        found_here = False
        for node in ast.walk(tree):
            if isinstance(node, ast.Name) and node.id == func_name:
                found_here = True
                break
            if isinstance(node, ast.Attribute) and node.attr == func_name:
                found_here = True
                break

        if found_here:
            usages.append(path)

    return usages


def remove_function_block(text: str, func_name: str) -> str:
    """Rimuove il blocco di definizione di una funzione a livello top.

    Match approssimativo:
    \ndef func_name(...):
        ...
    (fino al prossimo def/class/if __name__ o EOF)

    Se non trova nulla, restituisce il testo inalterato.
    """
    pattern = (
        r"\ndef " + re.escape(func_name) + r"\([\\s\\S]*?"
        r"(?=\n(?:def |class |if __name__|@|# ===|\Z))"
    )

    new_text, n = re.subn(pattern, "\n", text)
    if n == 0:
        print(f"[INFO] Nessun blocco trovato per {func_name} (forse già rimosso).")
        return text

    print(f"[INFO] Rimossi {n} blocchi per {func_name}.")
    return new_text


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    meta_path = root / "loventre_meta_decision_engine.py"

    if not meta_path.exists():
        raise SystemExit(
            f"[ERROR] File loventre_meta_decision_engine.py non trovato in {root}"
        )

    print(f"[INFO] Root progetto: {root}")
    print(f"[INFO] File meta-engine: {meta_path}")

    # 1) Controllo utilizzi esterni
    for func_name in LEGACY_FUNCTIONS:
        usages = find_usages(root, func_name)
        if usages:
            print(f"[WARN] Trovati utilizzi di {func_name} in altri file:")
            for p in usages:
                print(f"  - {p.relative_to(root)}")
            print(
                "[ABORT] Patch annullata: esistono riferimenti a funzioni legacy.\n"
                "        Valuta prima se rimuovere/aggiornare questi riferimenti."
            )
            raise SystemExit(1)

    # 2) Carico il meta-engine
    try:
        original_text = meta_path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as e:
        raise SystemExit(f"[ERROR] Impossibile leggere {meta_path}: {e}")

    patched_text = original_text

    # 3) Rimuovo le definizioni legacy (se presenti)
    for func_name in LEGACY_FUNCTIONS:
        patched_text = remove_function_block(patched_text, func_name)

    if patched_text == original_text:
        print("[INFO] Nessuna modifica effettuata (funzioni già assenti?).")
        return

    # 4) Verifico la sintassi con ast.parse
    try:
        ast.parse(patched_text, filename=str(meta_path))
    except SyntaxError as e:
        print("[ERROR] La sintassi dopo la patch non è valida, annullo la modifica.")
        print(f"        Dettagli: {e}")
        raise SystemExit(1)

    # 5) Scrivo il file patchato
    backup_path = meta_path.with_suffix(".py.bak_legacy_removal")
    try:
        if not backup_path.exists():
            backup_path.write_text(original_text, encoding="utf-8")
            print(f"[INFO] Backup creato in: {backup_path.name}")
    except OSError as e:
        print(f"[WARN] Impossibile creare backup {backup_path}: {e}")

    try:
        meta_path.write_text(patched_text, encoding="utf-8")
    except OSError as e:
        raise SystemExit(f"[ERROR] Impossibile scrivere {meta_path}: {e}")

    print("[OK] Patch applicata con successo a loventre_meta_decision_engine.py.")
    print("[OK] Le funzioni legacy non risultano più nel file.")


if __name__ == "__main__":
    main()

