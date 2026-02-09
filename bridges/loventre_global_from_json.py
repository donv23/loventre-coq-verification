#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
loventre_global_from_json.py

CLI di servizio per:
  1. leggere una istanza da JSON (seed_grid / SAT / TSP / famiglie critiche),
  2. chiamare l'entry point globale loventre_global_decide_with_policy(**kwargs),
  3. salvare le metriche (Loventre Metrics Bus + Policy Bridge) in un JSON,
  4. opzionalmente chiamare la CLI Coq bridge per generare uno snippet LMetrics.

NOTA (Dicembre 2025)
--------------------
Per massima robustezza:
- leggiamo dal JSON i campi (family, param, factor, ...),
- costruiamo un dizionario family_cfg,
- e passiamo al motore:
    family = family_cfg   (dict, non string),
    E, history.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
import sys
import traceback
from typing import Any, Dict

from loventre_global_entrypoint import loventre_global_decide_with_policy

ENGINE_ROOT = pathlib.Path(__file__).resolve().parent


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Loventre – GLOBAL ENTRYPOINT\n"
            "Legge una istanza da JSON, chiama il motore globale e salva le metriche.\n"
            "Opzionalmente invoca la CLI Coq bridge per generare un LMetrics snippet."
        )
    )
    parser.add_argument(
        "--instance-json",
        required=True,
        help="File JSON con la descrizione dell'istanza (es. instance_seed_grid_demo.json).",
    )
    parser.add_argument(
        "--metrics-out",
        default=None,
        help=(
            "File di output per le metriche (default: "
            "'metrics_<nome_instance>_global.json')."
        ),
    )
    parser.add_argument(
        "--def-name",
        default=None,
        help=(
            "Nome della Definition Coq LMetrics da usare nella CLI bridge "
            "(es. m_seed_grid_demo). Se omesso, la parte Coq viene saltata."
        ),
    )
    return parser.parse_args()


def load_instance_json(path: pathlib.Path) -> Dict[str, Any]:
    try:
        with path.open("r", encoding="utf-8") as f:
            data = json.load(f)
    except json.JSONDecodeError as exc:
        print(
            f"[ERRORE] JSON non valido in {path.name}: "
            f"{exc.msg} (posizione: line {exc.lineno} col {exc.colno})"
        )
        raise SystemExit(1)
    return data


def build_kwargs_from_instance(instance_cfg: Dict[str, Any]) -> Dict[str, Any]:
    """
    Converte il dict letto dal JSON in kwargs per loventre_global_decide_with_policy.

    Regole (Dicembre 2025, seed di stato):
    - 'family' nel JSON è il nome (es. "seed_grid"),
    - opzionalmente abbiamo param, factor, ecc.,
    - costruiamo un dict family_cfg e LO passiamo come 'family' al motore,
      perché il wrapper globale (o il motore) si aspetta un oggetto con .get(...)
      (da qui l'errore 'str' object has no attribute get).
    - E ha default 0.5 se assente,
    - history deve essere una lista NON VUOTA,
      il cui ultimo elemento è un dict (stato) su cui si può fare .get(...).
    """
    raw: Dict[str, Any] = dict(instance_cfg)  # copia superficiale

    if "family" not in raw:
        raise SystemExit(
            "[ERRORE] L'istanza JSON deve contenere almeno il campo 'family'. "
            'Esempio: {"family": "seed_grid", "param": 2, "factor": 2}'
        )

    # Energia (default 0.5)
    E_value = raw.get("E", 0.5)

    # History: garantiamo che sia una lista NON VUOTA di dict
    history_raw = raw.get("history")

    if history_raw is None:
        # Bootstrap minimale: un solo stato-dizionario “vuoto ma valido”
        history = [{"note": "bootstrap_from_json"}]
    else:
        if isinstance(history_raw, list):
            # Se è una lista di dizionari ed il LAST è un dict, lo teniamo
            if history_raw and isinstance(history_raw[-1], dict):
                history = history_raw
            else:
                # Lista ma ultimo elemento non è dict: lo wrappiamo
                history = [{"note": str(history_raw[-1])}]
        elif isinstance(history_raw, dict):
            history = [history_raw]
        else:
            # Stringa o altro: wrappiamo in un dict "note"
            history = [{"note": str(history_raw)}]

    # family_name + param/factor dal JSON
    family_name = raw.get("family", "seed_grid")
    param = raw.get("param")
    factor = raw.get("factor")

    # Costruiamo un oggetto “family_cfg” che il motore può interrogare con .get(...)
    family_cfg: Dict[str, Any] = {
        "family": family_name,
    }
    if param is not None:
        family_cfg["param"] = param
    if factor is not None:
        family_cfg["factor"] = factor

    kwargs: Dict[str, Any] = {
        "family": family_cfg,
        "E": E_value,
        "history": history,
    }

    return kwargs


def call_loventre_global(kwargs: Dict[str, Any]) -> Dict[str, Any]:
    print("--------------------------------------------------------------------")
    print("[INFO] Chiamo loventre_global_decide_with_policy(**kwargs) con:")
    for k in sorted(kwargs.keys()):
        print(f"  - {k} = {kwargs[k]!r}")
    print("--------------------------------------------------------------------")

    try:
        metrics = loventre_global_decide_with_policy(**kwargs)
    except Exception as exc:  # noqa: BLE001
        print("[ERRORE] Eccezione durante loventre_global_decide_with_policy(**kwargs):")
        print(f"Tipo    : {type(exc).__name__}")
        print(f"Dettaglio: {exc}")
        print()
        print("[TRACEBACK COMPLETO]")
        traceback.print_exc()
        raise SystemExit(1) from exc

    if not isinstance(metrics, dict):
        print(
            "[ERRORE] loventre_global_decide_with_policy non ha restituito un dict "
            f"ma: {type(metrics)!r}"
        )
        raise SystemExit(1)

    return metrics


def save_metrics(metrics: Dict[str, Any], out_path: pathlib.Path) -> None:
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8") as f:
        json.dump(metrics, f, indent=2, sort_keys=True, ensure_ascii=False)
    print(f"[INFO] Metrics Loventre salvate in: {out_path}")


def run_coq_bridge_if_requested(metrics_path: pathlib.Path, def_name: str) -> None:
    cli_bridge = ENGINE_ROOT / "loventre_metrics_cli_coq_bridge.py"
    if not cli_bridge.is_file():
        print(
            f"[WARN] CLI Coq bridge non trovata in {cli_bridge}.\n"
            "       Salto la parte di generazione snippet Coq.\n"
            "       Puoi comunque usare manualmente il file metrics_*.json."
        )
        return

    cmd = [
        sys.executable,
        str(cli_bridge),
        "--metrics-json",
        str(metrics_path),
        "--def-name",
        def_name,
    ]

    print()
    print("====================================================================")
    print("=== LOVENTRE – Lancio CLI Coq Bridge                            ===")
    print("====================================================================")
    print("[CMD]", " ".join(cmd))
    print()

    try:
        subprocess.run(cmd, check=False)
    except Exception as exc:  # noqa: BLE001
        print("[WARN] Errore durante l'esecuzione della CLI Coq bridge:")
        print(f"Tipo    : {type(exc).__name__}")
        print(f"Dettaglio: {exc}")


def main() -> None:
    args = parse_args()

    instance_path = (ENGINE_ROOT / args.instance_json).resolve()
    if not instance_path.is_file():
        print(f"[ERRORE] File istanza non trovato: {instance_path}")
        raise SystemExit(1)

    if args.metrics_out:
        metrics_path = (ENGINE_ROOT / args.metrics_out).resolve()
    else:
        metrics_path = ENGINE_ROOT / f"metrics_{instance_path.stem}_global.json"

    print()
    print("====================================================================")
    print("=== LOVENTRE GLOBAL ENTRYPOINT – JSON → metrics (+ Policy)      ===")
    print("====================================================================")
    print(f"Instance JSON : {instance_path.name}")
    if args.def_name:
        print(f"Coq def name  : {args.def_name}")
    else:
        print("Coq def name  : (nessuno, CLI Coq bridge NON verrà lanciata)")
    print("--------------------------------------------------------------------")

    instance_cfg = load_instance_json(instance_path)
    kwargs = build_kwargs_from_instance(instance_cfg)
    metrics = call_loventre_global(kwargs)
    save_metrics(metrics, metrics_path)

    if args.def_name:
        run_coq_bridge_if_requested(metrics_path, args.def_name)

    print()
    print("=== FINE LOVENTRE GLOBAL ENTRYPOINT (JSON → metrics) ===")


if __name__ == "__main__":
    main()

