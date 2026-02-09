from __future__ import annotations

import ast
from pathlib import Path


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    target = root / "loventre_meta_decision_cli.py"

    if not target.exists():
        print("[patch] File loventre_meta_decision_cli.py non trovato.")
        return

    text = target.read_text(encoding="utf-8")

    # Se la patch è già applicata, non facciamo nulla.
    if "_print_planck_layer_section(result)" in text:
        print("[patch] Planck layer già integrato nel CLI; nessuna modifica necessaria.")
        return

    # Sanity check iniziale: il file deve essere Python valido
    try:
        ast.parse(text)
    except SyntaxError as e:  # noqa: BLE001
        print(f"[patch] SyntaxError nel file originale, patch abortita: {e}")
        return

    old_block = "    print(explanation)\n    try:\n"
    new_block = "    print(explanation)\n    _print_planck_layer_section(result)\n    try:\n"

    if old_block not in text:
        print("[patch] Pattern atteso non trovato; struttura di _print_meta_report cambiata?")
        return

    new_text = text.replace(old_block, new_block)

    # Sanity check finale: il nuovo testo deve essere ancora Python valido
    try:
        ast.parse(new_text)
    except SyntaxError as e:  # noqa: BLE001
        print(f"[patch] SyntaxError dopo la patch, abort: {e}")
        return

    target.write_text(new_text, encoding="utf-8")
    print("[patch] _print_planck_layer_section collegato a _print_meta_report.")


if __name__ == "__main__":
    main()

