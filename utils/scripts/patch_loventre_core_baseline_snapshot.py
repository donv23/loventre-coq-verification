#!/usr/bin/env python3
"""
Patch Loventre core baseline snapshot:

- Aggiunge _snapshot_loventre_core_baseline(metrics) in loventre_meta_decision_engine.py
- Collega l'helper dentro meta_decide_instance_with_mass(...) prima del layer Schwarzschild.

Proprietà:
- idempotente (helper e call aggiunti solo se non presenti)
- validato con ast.parse prima e dopo
"""
import ast
import pathlib
import re
import sys
import textwrap


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

    updated = original

    # 1. Helper _snapshot_loventre_core_baseline se assente
    if "_snapshot_loventre_core_baseline" not in updated:
        helper_block = textwrap.dedent("""
        def _snapshot_loventre_core_baseline(metrics: dict) -> dict:
            \"""
            Cattura un baseline esplicito del core Loventre + massa.
            Popola chiavi *_base solo se non già presenti.
            \"""
            core_keys = [
                "kappa_eff",
                "entropy_eff",
                "V0",
                "p_tunnel",
                "mass_mean",
                "chi",
                "risk_index",
            ]
            for name in core_keys:
                base_key = f"{name}_base"
                if name in metrics and base_key not in metrics:
                    metrics[base_key] = metrics[name]
            return metrics
        """)
        updated = updated.rstrip() + "\n\n" + helper_block + "\n"
        _safe_parse(updated, "after adding _snapshot_loventre_core_baseline")
    else:
        print("[INFO] Helper _snapshot_loventre_core_baseline already present; skipping helper injection.")

    # 2. Collega l'helper dentro meta_decide_instance_with_mass(...)
    try:
        module = ast.parse(updated)
    except SyntaxError as e:
        print(f"[ERROR] Cannot parse updated file AST: {e}")
        sys.exit(1)

    func_node = None
    for node in module.body:
        if isinstance(node, ast.FunctionDef) and node.name == "meta_decide_instance_with_mass":
            func_node = node
            break

    if func_node is None:
        print("[WARN] meta_decide_instance_with_mass not found; nothing wired.")
        if updated != original:
            target.write_text(updated, encoding="utf-8")
            print("[OK] Helper injected, but no wiring applied.")
        return

    try:
        func_src = ast.get_source_segment(updated, func_node)
    except Exception as e:
        print(f"[ERROR] Could not extract function source: {e}")
        sys.exit(1)

    if not func_src:
        print("[WARN] Empty meta_decide_instance_with_mass source; nothing wired.")
        if updated != original:
            target.write_text(updated, encoding="utf-8")
            print("[OK] Helper injected, meta_decide_instance_with_mass untouched.")
        return

    # Idempotenza: se la chiamata è già presente, non modifichiamo nulla
    if "_snapshot_loventre_core_baseline(metrics)" in func_src:
        print("[INFO] meta_decide_instance_with_mass already calls _snapshot_loventre_core_baseline; nothing to change.")
        if updated != original:
            target.write_text(updated, encoding="utf-8")
            print("[OK] Helper ensured, no wiring changes needed.")
        return

    new_func_src = func_src

    # Cerchiamo la prima chiamata a append_schwarzschild_layer_to_metrics
    pattern = r"\n(\s*)(?:metrics\s*=\s*)?append_schwarzschild_layer_to_metrics\s*\(metrics\)"
    m = re.search(pattern, func_src)
    if m:
        indent = m.group(1) or "    "
        injection_line = f"\n{indent}metrics = _snapshot_loventre_core_baseline(metrics)"
        insert_pos = m.start()
        new_func_src = func_src[:insert_pos] + injection_line + func_src[insert_pos:]
    else:
        # Fallback: inseriamo prima dell'ultimo return metrics
        return_pattern = r"\n(\s*)return\s+metrics\b"
        matches = list(re.finditer(return_pattern, func_src))
        if not matches:
            print("[WARN] No 'return metrics' in meta_decide_instance_with_mass; wiring skipped.")
            if updated != original:
                target.write_text(updated, encoding="utf-8")
                print("[OK] Helper injected, but wiring could not be added.")
            return
        last = matches[-1]
        indent = last.group(1) or "    "
        injection_line = f"\n{indent}metrics = _snapshot_loventre_core_baseline(metrics)"
        insert_pos = last.start()
        new_func_src = func_src[:insert_pos] + injection_line + func_src[insert_pos:]

    if new_func_src == func_src:
        print("[WARN] Wiring produced no changes.")
        if updated != original:
            target.write_text(updated, encoding="utf-8")
            print("[OK] Helper injected, wiring noop.")
        return

    final_src = updated.replace(func_src, new_func_src, 1)
    _safe_parse(final_src, "final patched loventre_meta_decision_engine.py")

    if final_src != original:
        target.write_text(final_src, encoding="utf-8")
        print("[OK] Loventre core baseline snapshot wired into meta_decide_instance_with_mass")
    else:
        print("[OK] Nothing changed; file already in desired state.")


if __name__ == "__main__":
    main()

