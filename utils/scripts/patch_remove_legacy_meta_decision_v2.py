#!/usr/bin/env python3
"""
patch_remove_legacy_meta_decision_v2.py

Rimuove in modo sicuro e idempotente le funzioni legacy:
  - _append_policy_bridge_to_metrics_inline_legacy
  - _meta_decide_instance_with_mass_mass_layer_only
dal file loventre_meta_decision_engine.py senza toccare il resto.

Strategia:
  * lavora a livello di testo,
  * elimina il blocco 'def ...' + corpo indentato,
  * si ferma al primo statement top-level successivo,
  * verifica la sintassi con ast.parse prima di scrivere.
"""

from __future__ import annotations

import ast
from pathlib import Path


LEGACY_FUNCS = [
    "_append_policy_bridge_to_metrics_inline_legacy",
    "_meta_decide_instance_with_mass_mass_layer_only",
]


def remove_function_block(source: str, func_name: str) -> tuple[str, bool]:
    """
    Rimuove dal sorgente la definizione top-level di def func_name(...):
    e tutto il suo corpo (linee indentate) fino al successivo statement
    top-level non vuoto (qualunque cosa sia: def, commento, ecc.).

    Restituisce (nuovo_sorgente, removed_flag).
    """
    lines = source.splitlines(keepends=True)
    new_lines = []

    skipping = False
    removed = False

    for line in lines:
        if not skipping:
            # Siamo fuori da un blocco da rimuovere.
            stripped = line.lstrip()
            if line.startswith("def ") and stripped.startswith(f"def {func_name}("):
                # Trovata la definizione top-level della funzione legacy.
                skipping = True
                removed = True
                # Non aggiungiamo questa linea ai new_lines.
                continue
            else:
                new_lines.append(line)
        else:
            # Siamo dentro al blocco della funzione da rimuovere.
            if line.strip() == "":
                # Linea vuota subito dopo il corpo: eliminiamo per pulizia.
                continue

            # Calcoliamo indentazione corrente.
            indent = len(line) - len(line.lstrip(" "))
            if indent == 0:
                # Nuovo statement top-level: la funzione è finita.
                skipping = False
                # Questa linea NON fa parte della funzione: la teniamo.
                new_lines.append(line)
            else:
                # Linea ancora indentata: corpo della funzione -> scartiamo.
                continue

    return "".join(new_lines), removed


def main() -> None:
    root = Path(__file__).resolve().parent.parent
    target = root / "loventre_meta_decision_engine.py"

    if not target.exists():
        print(f"[ERRORE] File non trovato: {target}")
        return

    original_text = target.read_text(encoding="utf-8")

    print(f"[INFO] Root progetto: {root}")
    print(f"[INFO] File meta-engine: {target}")

    new_text = original_text
    total_removed = 0

    for fname in LEGACY_FUNCS:
        new_text, removed = remove_function_block(new_text, fname)
        if removed:
            print(f"[INFO] Funzione legacy rimossa: {fname}")
            total_removed += 1
        else:
            print(f"[INFO] Nessun blocco trovato per {fname} (forse già rimosso).")

    if total_removed == 0:
        print("[INFO] Nessuna modifica effettuata (funzioni legacy assenti).")
        return

    # Verifica di sintassi prima di scrivere.
    try:
        ast.parse(new_text, filename=str(target))
    except SyntaxError as e:
        print("[ERRORE] La patch produrrebbe un file non valido sintatticamente.")
        print(f"         Dettagli: {e}")
        print("[ERRORE] Il file NON è stato modificato.")
        return

    # Scriviamo il nuovo contenuto solo se la sintassi è ok.
    target.write_text(new_text, encoding="utf-8")
    print(f"[OK] Patch applicata. Funzioni legacy rimosse: {total_removed}.")


if __name__ == "__main__":
    main()

