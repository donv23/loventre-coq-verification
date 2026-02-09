#!/usr/bin/env python3
"""
Loventre CLI Coq Bridge – Demo multipla

Scopo:
  - Mostrare come, a partire da vari metrics_*.json, si possa ottenere
    uno snippet Coq LMetrics corrispondente (definizione m_*_cli_demo).
  - Integrare in modo uniforme i witness P_like / NP_like_critici
    (seed11, TSPcrit28, SATcrit16) e il seed_grid P_like_accessible.

Questo script è solo una demo orchestratrice: delega il lavoro vero a
  loventre_metrics_cli_coq_bridge.py
che legge il JSON e stampa il relativo snippet Coq.
"""

import pathlib
import subprocess
import sys


ROOT = pathlib.Path(__file__).resolve().parent


def run_case(metrics_name: str, def_name: str) -> None:
    """
    Esegue il bridge CLI per un singolo file metrics_*.json, usando
    loventre_metrics_cli_coq_bridge.py e stampando un header leggibile.
    """
    print("\n" + "=" * 80)
    print(
        f"=== DEMO CASE: metrics = {metrics_name} → Coq def = {def_name} ==="
    )
    print("=" * 80)

    cmd = [
        sys.executable,
        "loventre_metrics_cli_coq_bridge.py",
        "--metrics-json",
        metrics_name,
        "--def-name",
        def_name,
    ]

    print(f"[CMD] {' '.join(cmd)}")
    print("")

    # Eseguiamo il comando nella root del motore.
    subprocess.run(cmd, cwd=ROOT, check=True)


def main() -> None:
    print("=" * 70)
    print("=== LOVENTRE DEMO – CLI Coq Bridge (metrics → LMetrics → snippet) ===")
    print("=" * 70)
    print("")

    demos = [
        # Witness P_like / SAFE (seed11)
        ("metrics_seed11_cli_demo.json", "m_seed11_cli_demo"),
        # Witness NP_like_critico (TSPcrit28)
        ("metrics_TSP_crit28_demo.json", "m_TSPcrit28_cli_demo"),
        # Witness NP_like_critico (SATcrit16)
        ("metrics_SAT_crit16_demo.json", "m_SATcrit16_cli_demo"),
        # Nuovo witness P_like_accessible (seed_grid, configurazione globale)
        ("metrics_seed_grid_demo_global.json", "m_seed_grid_demo"),
    ]

    for metrics_name, def_name in demos:
        run_case(metrics_name, def_name)

    print("")
    print("=== END DEMO CLI COQ BRIDGE ===")


if __name__ == "__main__":
    main()

