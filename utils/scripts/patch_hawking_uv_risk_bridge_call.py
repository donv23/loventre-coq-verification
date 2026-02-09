#!/usr/bin/env python3
"""
Second stage patch Hawking UV → Policy Bridge:

- Localizza la funzione apply_policy_bridge_to_metrics(...)
- Inserisce la chiamata:

    metrics = _compute_hawking_uv_risk_coupling(metrics)

subito prima dell'ultimo `return ...` della funzione.

Proprietà:
- Idempotente: se la chiamata è già presente, non fa nulla.
- Validato con ast.parse prima e dopo.
"""
import ast
import pathlib
import re
import sys


def _safe_parse(src: str, label: str) -> None:
    try:
        ast.parse(src)
    except SyntaxError as e:
        print(f"[ERROR] Syntax error while parsing {label}: {e}")
        sys.exit(1)


def main() -> None:
    root = pathlib.Path(__file__).resolve().parents[1]
    target = root / "loventre_meta_decision_engine.py"

    if not target.exists():
        print(f"[ERROR] Target file not found: {target}")
        sys.exit(1)

    original = target.read_text(encoding="utf-8")
    _safe_parse(original, "original loventre_meta_decision_engine.py")

    try:
        module = ast.parse(original)
    except SyntaxError as e:
        print(f"[ERROR] Cannot parse target file AST: {e}")
        sys.exit(1)

    func_node = None
    for node in module.body:
        if isinstance(node, ast.FunctionDef) and node.name == "apply_policy_bridge_to_metrics":
            func_node = node
            break

    if func_node is None:
        print("[WARN] apply_policy_bridge_to_metrics not found; nothing changed.")
        return

    # Estrae il sorgente originale della funzione
    try:
        func_src = ast.get_source_segment(original, func_node)
    except Exception as e:
        print(f"[ERROR] Could not extract function source: {e}")
        return

    if not func_src:
        print("[WARN] Empty function source; nothing changed.")
        return

    # Idempotenza: se la chiamata è già presente, usciamo
    if "_compute_hawking_uv_risk_coupling(metrics)" in func_src:
        print("[INFO] Hawking UV risk coupling already wired into Policy Bridge; nothing to change.")
        return

    # Trova l'ultimo `return` nella funzione
    return_pattern = r"\n(\s*)return\b"
    matches = list(re.finditer(return_pattern, func_src))
    if not matches:
        print("[WARN] No 'return' statement found in apply_policy_bridge_to_metrics; nothing changed.")
        return

    last = matches[-1]
    indent = last.group(1) or "    "
    call_line = f"\n{indent}metrics = _compute_hawking_uv_risk_coupling(metrics)"

    insert_pos = last.start()
    new_func_src = func_src[:insert_pos] + call_line + func_src[insert_pos:]

    # Ricostruisce il sorgente globale sostituendo solo questa funzione
    updated = original.replace(func_src, new_func_src, 1)
    if updated == original:
        print("[WARN] Replacement did not modify source; nothing changed.")
        return

    _safe_parse(updated, "patched loventre_meta_decision_engine.py")

    target.write_text(updated, encoding="utf-8")
    print("[OK] Wired Hawking UV risk coupling into apply_policy_bridge_to_metrics")


if __name__ == "__main__":
    main()

