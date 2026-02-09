"""
run_loventre_regression_suite.py

Suite di regressione per il Loventre Engine Python (stato: dicembre 2025).

Scopo:
  - Eseguire in sequenza le demo chiave del motore
    per verificare che dopo modifiche strutturali
    il comportamento globale resti sano.
  - Verificare la coerenza di alcuni JSON di metrics
    considerati "witness" o famiglie canoniche (es. 2-SAT).
  - Verificare la coerenza tra i witness JSON canonici
    (witness_json/*.json) e il file Coq di link
    Loventre_LMetrics_JSON_Link.v, tramite
    loventre_json_crosscheck_coq.py.

Demo considerate:
  - loventre_meta_portfolio_lab.py
  - loventre_global_profile_lab.py
  - demo_seed_global_decision.py
  - demo_critfam_global_decision.py
  - demo_mass_global_run.py
  - demo_global_entrypoint.py
  - demo_cli_coq_bridge.py

Check JSON (prima tranche, 2-SAT family):
  - metrics_2SAT_easy_demo.json
      * meta_label                         = meta_P_like_like
      * risk_class                         = LOW
      * horizon_flag                       = False
      * loventre_global.global_decision    = SAFE
      * loventre_global.global_color       = GREEN
  - metrics_2SAT_crit_demo.json
      * meta_label                         = meta_P_like_accessible
      * risk_class                         = LOW
      * horizon_flag                       = False
      * loventre_global.global_decision    = BORDERLINE
      * loventre_global.global_color       = GREEN

Check JSON ↔ Coq (witness canonici LMetrics):
  - loventre_json_crosscheck_coq.py
      * verifica che per ogni lm_id_link in
        Loventre_LMetrics_JSON_Link.v esista un JSON corrispondente
        in witness_json/<lm_id>.json, e viceversa.

Per ogni script demo:
  - se il file non esiste: [SKIP]
  - se esiste:
      * viene eseguito con il Python corrente
      * se exit code != 0 → [FAIL]
      * se exit code == 0 → [OK]

Per ogni JSON (2-SAT):
  - se il file non esiste: [SKIP_JSON]
  - se esiste:
      * viene caricato
      * i campi chiave vengono confrontati con i target
      * mismatch → [FAIL_JSON]
      * tutto coerente → [ OK_JSON ]

Per il crosscheck JSON ↔ Coq:
  - se lo script non esiste: [SKIP_CQ]
  - se esiste:
      * viene eseguito e il suo output analizzato
      * se compaiono [MISS], [EXTRA], [ERR] o warning critici
        → [FAIL_CQ]
      * se non compaiono mismatch → [ OK_CQ ]

Uso:
  python3 run_loventre_regression_suite.py
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Dict, Any, List, Tuple


def run_demo_scripts(base_dir: Path) -> Tuple[List[str], List[str]]:
    demo_scripts = [
        "loventre_meta_portfolio_lab.py",
        "loventre_global_profile_lab.py",
        "demo_seed_global_decision.py",
        "demo_critfam_global_decision.py",
        "demo_mass_global_run.py",
        "demo_global_entrypoint.py",
        "demo_cli_coq_bridge.py",
    ]

    failed: List[str] = []
    skipped: List[str] = []

    print("[Loventre] Avvio suite di regressione demo...\n")

    for name in demo_scripts:
        script_path = base_dir / name

        if not script_path.exists():
            msg = f"[SKIP] {name} (file non trovato in {base_dir})"
            print(msg)
            skipped.append(name)
            continue

        print(f"[RUN ] {name}")
        try:
            result = subprocess.run(
                [sys.executable, str(script_path)],
                check=False,
            )
        except Exception as exc:  # pragma: no cover
            print(f"[FAIL] {name} ha lanciato un'eccezione: {exc!r}")
            failed.append(name)
            continue

        if result.returncode != 0:
            print(f"[FAIL] {name} exit code: {result.returncode}")
            failed.append(name)
        else:
            print(f"[ OK ] {name}")

        print("-" * 60)

    return failed, skipped


def _load_json(path: Path) -> Dict[str, Any]:
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def _check_field_equality(
    label: str,
    data: Dict[str, Any],
    key: str,
    expected: Any,
    errors: List[str],
) -> None:
    actual = data.get(key, None)
    if actual != expected:
        errors.append(
            f"{label}: campo '{key}' atteso={expected!r}, trovato={actual!r}"
        )


def _check_field_bool(
    label: str,
    data: Dict[str, Any],
    key: str,
    expected: bool,
    errors: List[str],
) -> None:
    actual = data.get(key, None)
    if bool(actual) is not expected:
        errors.append(
            f"{label}: campo booleano '{key}' atteso={expected!r}, trovato={actual!r}"
        )


def run_2sat_json_checks(base_dir: Path) -> Tuple[List[str], List[str]]:
    """
    Verifica i witness JSON della famiglia 2-SAT, generati da
    build_metrics_2sat_family.py.

    Non controlla tutti i campi del bus, ma solo quelli chiave
    per la semantica P_like / Pacc_Lov / SAFE / borderline.
    """
    print("\n[Loventre] Check JSON – Famiglia 2-SAT\n")

    json_targets = [
        (
            "metrics_2SAT_easy_demo.json",
            {
                "meta_label": "meta_P_like_like",
                "risk_class": "LOW",
                "loventre_global_decision": "SAFE",
                "loventre_global_color": "GREEN",
                "horizon_flag": False,
            },
        ),
        (
            "metrics_2SAT_crit_demo.json",
            {
                "meta_label": "meta_P_like_accessible",
                "risk_class": "LOW",
                "loventre_global_decision": "BORDERLINE",
                "loventre_global_color": "GREEN",
                "horizon_flag": False,
            },
        ),
    ]

    failed: List[str] = []
    skipped: List[str] = []

    for filename, expectations in json_targets:
        label = f"JSON:{filename}"
        path = base_dir / filename

        if not path.exists():
            print(f"[SKIP_JSON] {filename} (file non trovato)")
            skipped.append(filename)
            continue

        try:
            data = _load_json(path)
        except Exception as exc:  # pragma: no cover
            print(f"[FAIL_JSON] {filename} – errore nel parsing JSON: {exc!r}")
            failed.append(filename)
            continue

        errors: List[str] = []

        # Campi stringa diretti
        _check_field_equality(
            label, data, "meta_label", expectations["meta_label"], errors
        )
        _check_field_equality(
            label, data, "risk_class", expectations["risk_class"], errors
        )

        # Campi nidificati sotto loventre_global
        lg = data.get("loventre_global")
        if not isinstance(lg, dict):
            errors.append(
                f"{label}: sezione 'loventre_global' mancante o non è un dict"
            )
        else:
            gd_actual = lg.get("global_decision", None)
            if gd_actual != expectations["loventre_global_decision"]:
                errors.append(
                    f"{label}: campo 'loventre_global.global_decision' atteso={expectations['loventre_global_decision']!r}, trovato={gd_actual!r}"
                )

            gc_actual = lg.get("global_color", None)
            if gc_actual != expectations["loventre_global_color"]:
                errors.append(
                    f"{label}: campo 'loventre_global.global_color' atteso={expectations['loventre_global_color']!r}, trovato={gc_actual!r}"
                )

        # Campo booleano horizon_flag
        _check_field_bool(
            label, data, "horizon_flag", expectations["horizon_flag"], errors
        )

        # Controllo blando su P_success: deve essere alta (>= 0.9)
        p_success = data.get("P_success", None)
        if not isinstance(p_success, (int, float)) or p_success < 0.9:
            errors.append(
                f"{label}: P_success attesa >= 0.9, trovata={p_success!r}"
            )

        if errors:
            print(f"[FAIL_JSON] {filename}")
            for e in errors:
                print("   -", e)
            failed.append(filename)
        else:
            lg = data.get("loventre_global", {}) or {}
            print(f"[ OK_JSON] {filename}")
            print(
                f"   meta_label={data.get('meta_label')}, "
                f"risk_class={data.get('risk_class')}, "
                f"decision={lg.get('global_decision')}, "
                f"color={lg.get('global_color')}, "
                f"P_success={data.get('P_success')}"
            )

    print()
    return failed, skipped


def run_json_coq_crosscheck(base_dir: Path) -> Tuple[bool, bool]:
    """
    Esegue lo script loventre_json_crosscheck_coq.py e analizza il suo output
    per rilevare mismatch fra:
      - lm_id_link elencati in Loventre_LMetrics_JSON_Link.v (Coq)
      - lm_id presenti nei witness JSON (witness_json/*.json)

    Restituisce:
      (failed, skipped)
        failed  = True se sono stati rilevati mismatch o errori
        skipped = True se lo script non è stato trovato
    """
    print("\n[Loventre] Check JSON ↔ Coq LMetrics (witness canonici)\n")

    script_name = "loventre_json_crosscheck_coq.py"
    script_path = base_dir / script_name

    if not script_path.exists():
        print(f"[SKIP_CQ] {script_name} (file non trovato in {base_dir})\n")
        return False, True

    try:
        result = subprocess.run(
            [sys.executable, str(script_path)],
            check=False,
            capture_output=True,
            text=True,
        )
    except Exception as exc:  # pragma: no cover
        print(f"[FAIL_CQ] {script_name} ha lanciato un'eccezione: {exc!r}")
        return True, False

    # Stampa l'output catturato per intero (stdout + stderr)
    if result.stdout:
        print(result.stdout, end="")
    if result.stderr:
        print("----- stderr -----")
        print(result.stderr)
        print("------------------")

    failed = False
    out = result.stdout or ""

    # Heuristica semplice: se compaiono queste etichette, consideriamo il check fallito.
    if "[MISS]" in out or "[EXTRA]" in out or "[ERR" in out:
        failed = True
        print("[FAIL_CQ] Crosscheck JSON ↔ Coq ha rilevato mismatch o errori.")
    elif "[WARN] Directory JSON non trovata" in out:
        failed = True
        print(
            "[FAIL_CQ] Crosscheck JSON ↔ Coq fallito: directory witness_json mancante."
        )
    else:
        print("[ OK_CQ] Crosscheck JSON ↔ Coq muto (nessun mismatch rilevato).")

    # In ogni caso, se lo script ha exit code non zero, segniamo fail.
    if result.returncode != 0:
        failed = True
        print(f"[FAIL_CQ] {script_name} exit code: {result.returncode}")

    print()
    return failed, False


def main() -> int:
    base_dir = Path(__file__).resolve().parent

    # 1) Demo script regression
    demo_failed, demo_skipped = run_demo_scripts(base_dir)

    # 2) JSON 2-SAT regression
    json_failed, json_skipped = run_2sat_json_checks(base_dir)

    # 3) JSON ↔ Coq crosscheck (witness canonici LMetrics)
    coq_json_failed, coq_json_skipped = run_json_coq_crosscheck(base_dir)

    print("\n[Loventre] Risultato suite di regressione")
    print("========================================")

    any_failed = bool(demo_failed or json_failed or coq_json_failed)

    if demo_failed:
        print("\nDemo FALLITE:")
        for name in demo_failed:
            print(f"  - {name}")
    else:
        print("\nNessuna demo fallita.")

    if demo_skipped:
        print("\nDemo SALTATE (file non presenti):")
        for name in demo_skipped:
            print(f"  - {name}")
    else:
        print("\nNessuna demo saltata.")

    if json_failed:
        print("\nJSON FALLITI (2-SAT family):")
        for name in json_failed:
            print(f"  - {name}")
    else:
        print("\nNessun JSON 2-SAT fallito.")

    if json_skipped:
        print("\nJSON SALTATI (file non presenti):")
        for name in json_skipped:
            print(f"  - {name}")
    else:
        print("\nNessun JSON 2-SAT saltato.")

    if coq_json_failed:
        print("\nCrosscheck JSON ↔ Coq FALLITO:")
        print("  - loventre_json_crosscheck_coq.py ha rilevato mismatch o errori.")
    elif coq_json_skipped:
        print("\nCrosscheck JSON ↔ Coq SALTATO (script non presente).")
    else:
        print("\nCrosscheck JSON ↔ Coq OK (nessun mismatch).")

    print("\nFine suite.\n")

    # exit code: 0 se tutto ok, 1 se c'è almeno un FAIL
    return 0 if not any_failed else 1


if __name__ == "__main__":
    raise SystemExit(main())

