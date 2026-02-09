from __future__ import annotations

import ast
from pathlib import Path


def main() -> None:
    path = Path("loventre_meta_decision_engine.py")
    if not path.exists():
        print(f"File non trovato: {path}")
        return

    code = path.read_text(encoding="utf-8")

    marker = "def append_schwarzschild_layer_to_metrics"
    idx_fun = code.find(marker)
    if idx_fun == -1:
        print("Funzione append_schwarzschild_layer_to_metrics non trovata; nessuna modifica.")
        return

    # Limitiamo la ricerca della riga a *dopo* la definizione di append_schwarzschild_layer_to_metrics
    tail = code[idx_fun:]
    target = "metrics = append_planck_layer_to_metrics(metrics)"
    idx_target = tail.find(target)
    if idx_target == -1:
        print(
            "Nessuna riga con 'metrics = append_planck_layer_to_metrics(metrics)' "
            "dentro append_schwarzschild_layer_to_metrics; niente da fare."
        )
        return

    abs_idx = idx_fun + idx_target

    # Trova inizio e fine della riga da rimuovere (incluso il newline)
    line_start = code.rfind("\n", 0, abs_idx)
    if line_start == -1:
        line_start = 0
    else:
        line_start += 1  # salta il '\n'

    line_end = code.find("\n", abs_idx)
    if line_end == -1:
        line_end = len(code)
    else:
        line_end += 1  # includi il '\n'

    new_code = code[:line_start] + code[line_end:]

    try:
        ast.parse(new_code)
    except SyntaxError as exc:
        print("Errore di sintassi dopo la patch; non ho toccato il file.")
        print("Dettaglio:", exc)
        return

    path.write_text(new_code, encoding="utf-8")
    print(
        "✅ Rimossa la chiamata interna a append_planck_layer_to_metrics "
        "da append_schwarzschild_layer_to_metrics."
    )


if __name__ == "__main__":
    main()

