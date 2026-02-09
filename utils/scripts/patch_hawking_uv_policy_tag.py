#!/usr/bin/env python3
"""
Patch Hawking UV → Policy Bridge (policy_uv_tag + commenti):

1. Aggiunge in loventre_meta_decision_engine.py un helper:

    _annotate_policy_with_hawking_uv(metrics: dict) -> dict

   che:
   - legge hawking_uv_phase, hawking_uv_index, (opz) risk_index
   - scrive:
        * policy_uv_tag
        * policy_uv_note
        * policy_uv_annotation
        * aggiorna policy_comment concatenando una nota UV

2. Collega l'helper dentro apply_policy_bridge_to_metrics(...)
   subito dopo la chiamata a _compute_hawking_uv_risk_coupling(metrics),
   se presente, altrimenti prima dell'ultimo return.

Proprietà:
- idempotente (se helper/call sono già presenti, non modifica nulla)
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

    # 1. Helper _annotate_policy_with_hawking_uv se assente
    if "_annotate_policy_with_hawking_uv" not in updated:
        helper_block = textwrap.dedent("""
        def _annotate_policy_with_hawking_uv(metrics: dict) -> dict:
            \"""
            Colora il Policy Bridge con un tag Hawking UV e una nota esplicativa.

            Legge:
                - hawking_uv_phase
                - hawking_uv_index
                - (opzionale) risk_index

            Scrive:
                - policy_uv_tag
                - policy_uv_note
                - policy_uv_annotation
                - policy_comment (esteso con un frammento UV)
            \"""
            if (
                "hawking_uv_phase" not in metrics
                and "hawking_uv_index" not in metrics
            ):
                # Nessuna informazione UV disponibile: non tocchiamo la policy.
                return metrics

            phase_raw = metrics.get("hawking_uv_phase", "unknown")
            try:
                phase = str(phase_raw or "unknown")
            except Exception:
                phase = "unknown"

            try:
                uv_index_val = float(metrics.get("hawking_uv_index") or 0.0)
            except Exception:
                uv_index_val = 0.0
            uv_index_val = max(0.0, uv_index_val)

            # Classificazione in tag qualitativi non banali
            if phase == "sub_uv" and uv_index_val < 1.0:
                uv_tag = "uv_quiet"
                uv_note = (
                    "regime Hawking UV quieto; la decisione resta dominata "
                    "dalla componente infrarossa."
                )
            elif phase == "sub_uv":
                uv_tag = "uv_latent"
                uv_note = (
                    "regime Hawking UV latente; segnali UV presenti ma non predominanti."
                )
            elif phase == "critical_uv" and uv_index_val < 10.0:
                uv_tag = "uv_edge"
                uv_note = (
                    "regime Hawking UV al bordo critico; transizioni possibili "
                    "ma ancora contenute."
                )
            elif phase == "critical_uv":
                uv_tag = "uv_critical"
                uv_note = (
                    "regime Hawking UV critico; la policy mantiene margini di sicurezza "
                    "rafforzati."
                )
            elif phase == "trans_uv" and uv_index_val < 10.0:
                uv_tag = "uv_active"
                uv_note = (
                    "regime Hawking UV attivo in transizione; consigliata cautela amplificata."
                )
            elif phase == "trans_uv":
                uv_tag = "uv_frontier"
                uv_note = (
                    "regime Hawking UV di frontiera; la policy entra in zona "
                    "di sperimentazione controllata."
                )
            else:
                uv_tag = "uv_unknown"
                uv_note = (
                    "regime Hawking UV non classificato; la policy mantiene "
                    "lo stato nominale."
                )

            metrics["policy_uv_tag"] = uv_tag
            metrics["policy_uv_note"] = uv_note

            # Prepariamo uno snippet UV compatto
            uv_snippet = f"[Hawking-UV: {uv_tag}, phase={phase}, index≈{uv_index_val:.3f}] {uv_note}"

            # Estensione morbida del policy_comment esistente
            base_comment = metrics.get("policy_comment", "")
            try:
                base_comment_str = str(base_comment) if base_comment is not None else ""
            except Exception:
                base_comment_str = ""

            if base_comment_str:
                new_comment = base_comment_str + " " + uv_snippet
            else:
                new_comment = uv_snippet

            metrics["policy_comment"] = new_comment
            metrics["policy_uv_annotation"] = uv_snippet

            return metrics
        """)
        updated = updated.rstrip() + "\n\n" + helper_block + "\n"
        _safe_parse(updated, "after adding _annotate_policy_with_hawking_uv")
    else:
        print("[INFO] Helper _annotate_policy_with_hawking_uv already present; skipping helper injection.")

    # 2. Collega l'helper dentro apply_policy_bridge_to_metrics(...)
    try:
        module = ast.parse(updated)
    except SyntaxError as e:
        print(f"[ERROR] Cannot parse updated file AST: {e}")
        sys.exit(1)

    func_node = None
    for node in module.body:
        if isinstance(node, ast.FunctionDef) and node.name == "apply_policy_bridge_to_metrics":
            func_node = node
            break

    if func_node is None:
        print("[WARN] apply_policy_bridge_to_metrics not found; nothing wired.")
        if updated != original:
            target.write_text(updated, encoding="utf-8")
            print("[OK] Helper injected, but Policy Bridge wiring skipped (function not found).")
        return

    try:
        func_src = ast.get_source_segment(updated, func_node)
    except Exception as e:
        print(f"[ERROR] Could not extract function source: {e}")
        sys.exit(1)

    if not func_src:
        print("[WARN] Empty apply_policy_bridge_to_metrics source; nothing wired.")
        if updated != original:
            target.write_text(updated, encoding="utf-8")
            print("[OK] Helper injected, Policy Bridge untouched.")
        return

    # Idempotenza: se la chiamata è già presente, non modifichiamo nulla
    if "metrics = _annotate_policy_with_hawking_uv(metrics)" in func_src:
        print("[INFO] Policy Bridge already calls _annotate_policy_with_hawking_uv; nothing to change.")
        if updated != original:
            target.write_text(updated, encoding="utf-8")
            print("[OK] Helper ensured, no wiring changes needed.")
        return

    new_func_src = func_src

    # Caso 1: la funzione contiene già la chiamata a _compute_hawking_uv_risk_coupling
    risk_call_pattern = r"\n(\s*)metrics\s*=\s*_compute_hawking_uv_risk_coupling\s*\(metrics\)"
    m = re.search(risk_call_pattern, func_src)
    if m:
        indent = m.group(1) or "    "
        injection_line = f"\n{indent}metrics = _annotate_policy_with_hawking_uv(metrics)"
        # Inseriamo subito DOPO la chiamata al risk coupling
        span = m.span()
        segment = func_src[span[0]:span[1]]
        replacement = segment + injection_line
        new_func_src = func_src.replace(segment, replacement, 1)
    else:
        # Caso 2: fallback, inseriamo prima dell'ultimo return della funzione
        return_pattern = r"\n(\s*)return\b"
        matches = list(re.finditer(return_pattern, func_src))
        if not matches:
            print("[WARN] No 'return' in apply_policy_bridge_to_metrics; wiring skipped.")
            if updated != original:
                target.write_text(updated, encoding="utf-8")
                print("[OK] Helper injected, Policy Bridge wiring could not be added.")
            return

        last = matches[-1]
        indent = last.group(1) or "    "
        injection_line = f"\n{indent}metrics = _annotate_policy_with_hawking_uv(metrics)"
        insert_pos = last.start()
        new_func_src = func_src[:insert_pos] + injection_line + func_src[insert_pos:]

    if new_func_src == func_src:
        print("[WARN] Policy Bridge wiring produced no changes.")
        if updated != original:
            target.write_text(updated, encoding="utf-8")
            print("[OK] Helper injected, Policy Bridge wiring noop.")
        return

    updated_final = updated.replace(func_src, new_func_src, 1)
    _safe_parse(updated_final, "final patched loventre_meta_decision_engine.py")

    if updated_final != original:
        target.write_text(updated_final, encoding="utf-8")
        print("[OK] Hawking UV policy tag wired into apply_policy_bridge_to_metrics")
    else:
        print("[OK] Nothing changed; file already in desired state.")


if __name__ == "__main__":
    main()

