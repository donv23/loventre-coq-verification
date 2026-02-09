#!/usr/bin/env python3
"""
Patch di integrazione Policy Bridge → meta_decide_instance_with_mass_global.

Effetti:
  1) Aggiunge (se manca) l'import nel modulo loventre_meta_decision_engine:

       from loventre_policy_bridge import append_policy_bridge_to_metrics

  2) Dentro la funzione meta_decide_instance_with_mass_global, sostituisce
     il 'return res' finale con:

       metrics = res.get("metrics")
       if isinstance(metrics, dict):
           append_policy_bridge_to_metrics(metrics)
       return res

Patch idempotente:
  - se trova già 'append_policy_bridge_to_metrics(metrics)' nel file
    non fa nulla.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys


def main() -> None:
    # scripts/ -> root dell'engine
    scripts_dir = Path(__file__).resolve().parent
    engine_root = scripts_dir.parent
    target = engine_root / "loventre_meta_decision_engine.py"

    if not target.exists():
        print(f"[ERRORE] File non trovato: {target}")
        sys.exit(1)

    text = target.read_text(encoding="utf-8")

    # Idempotenza: se abbiamo già la chiamata, usciamo.
    if "append_policy_bridge_to_metrics(metrics)" in text:
        print("[INFO] Patch già applicata (append_policy_bridge_to_metrics(metrics) trovato).")
        return

    # ------------------------------------------------------------
    # 1) Inserimento import del Policy Bridge se manca
    # ------------------------------------------------------------
    import_line = "from loventre_policy_bridge import append_policy_bridge_to_metrics\n"

    if import_line not in text:
        if "from __future__ import annotations" in text:
            text = text.replace(
                "from __future__ import annotations\n",
                "from __future__ import annotations\n\n" + import_line,
            )
        else:
            # Caso di fallback: in testa al file
            text = import_line + "\n" + text

    # ------------------------------------------------------------
    # 2) Patch della funzione meta_decide_instance_with_mass_global
    # ------------------------------------------------------------
    pattern = re.compile(
        r"(def\s+meta_decide_instance_with_mass_global[^\n]*:\n"
        r"(?:[ \t].*\n)*?)"          # corpo della funzione fino a prima del return
        r"([ \t]+)return\s+res\b",   # indent + 'return res'
        re.DOTALL,
    )

    def _repl(match: "re.Match[str]") -> str:
        before = match.group(1)
        indent = match.group(2)
        injected = (
            f"{indent}metrics = res.get(\"metrics\")\n"
            f"{indent}if isinstance(metrics, dict):\n"
            f"{indent}    append_policy_bridge_to_metrics(metrics)\n"
            f"{indent}return res"
        )
        return before + injected

    new_text, n_sub = pattern.subn(_repl, text, count=1)

    if n_sub == 0:
        print(
            "[ERRORE] Non sono riuscito a trovare il blocco "
            "'def meta_decide_instance_with_mass_global ... return res'."
        )
        print("       Verifica la struttura della funzione e riprova.")
        sys.exit(1)

    target.write_text(new_text, encoding="utf-8")
    print("[OK] Patch Policy Bridge applicata a loventre_meta_decision_engine.py")


if __name__ == "__main__":
    main()

