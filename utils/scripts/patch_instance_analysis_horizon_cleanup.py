from __future__ import annotations

from pathlib import Path
import re
import sys


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    target = root / "loventre_instance_analysis.py"

    code = target.read_text(encoding="utf-8")

    # Se troviamo già la versione legacy e NON troviamo più il wrapper,
    # assumiamo che la patch sia già stata applicata.
    if "_legacy_detect_complexity_horizon" in code and "_loventre_original_detect_complexity_horizon" not in code:
        print("Patch instance_analysis_horizon_cleanup: già applicata, nessuna modifica.")
        return

    new_code = code

    # 1) Rinominare la PRIMA definizione di detect_complexity_horizon in _legacy_detect_complexity_horizon
    new_code, n_renamed = re.subn(
        r"def\s+detect_complexity_horizon\(",
        "def _legacy_detect_complexity_horizon(",
        new_code,
        count=1,
    )

    if n_renamed == 0:
        print("ATTENZIONE: non ho trovato la definizione originale di detect_complexity_horizon.")
        # non usciamo ancora, potrebbe essere già stata rinominata in una fase precedente
        # ma continuiamo con il resto
    else:
        print("Rinominata la prima detect_complexity_horizon -> _legacy_detect_complexity_horizon.")

    # 2) Rimuovere il vecchio wrapper mass-aware basato su _loventre_original_detect_complexity_horizon
    start_marker = "# --- Loventre mass-aware refinement of detect_complexity_horizon (non-breaking wrapper) ---"
    end_marker = "# --- Loventre override: mass-aware detect_complexity_horizon ---"

    start = new_code.find(start_marker)
    end = new_code.find(end_marker)

    if start != -1 and end != -1 and start < end:
        # Conserviamo l'end_marker e tutto ciò che segue
        before = new_code[:start]
        after = new_code[end:]
        new_code = before + after
        print("Rimosso il vecchio wrapper _loventre_original_detect_complexity_horizon.")
    else:
        print("Wrapper mass-aware precedente non trovato (forse già rimosso).")

    # 3) Nell'esempio example_horizon_detection, usare la funzione legacy invece del nome pubblico
    new_code, n_example = re.subn(
        r"horizon_info\s*=\s*detect_complexity_horizon\(",
        "horizon_info = _legacy_detect_complexity_horizon(",
        new_code,
        count=1,
    )

    if n_example > 0:
        print("Aggiornato example_horizon_detection a usare _legacy_detect_complexity_horizon.")
    else:
        print("example_horizon_detection era già aggiornato o non è stato trovato.")

    # Se nessuna modifica effettiva, non sovrascriviamo il file
    if new_code == code:
        print("Patch instance_analysis_horizon_cleanup: nessuna modifica da applicare.")
        return

    # Scriviamo il nuovo contenuto
    target.write_text(new_code, encoding="utf-8")

    # Controllo sintassi
    try:
        compile(new_code, str(target), "exec")
    except SyntaxError as e:
        print("ERRORE: sintassi non valida dopo la patch:", e)
        sys.exit(1)

    print("Patch instance_analysis_horizon_cleanup applicata con successo. Sintassi OK.")


if __name__ == "__main__":
    main()

