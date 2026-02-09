#!/usr/bin/env python3
"""
Debug del baseline Loventre core:

- importa loventre_meta_decision_engine
- usa _snapshot_loventre_core_baseline(metrics) su casi sintetici
- mostra come vengono popolati i campi *_base e come i valori correnti
  possono poi essere deformati senza toccare il baseline.

NOTA: qui non usiamo l'intera pipeline, ma solo l'helper, per vedere
      chiaramente cosa fa sul dict metrics.
"""

import sys
import pathlib


def main() -> None:
    # Aggancia la root del progetto (.. rispetto a scripts/)
    root = pathlib.Path(__file__).resolve().parents[1]
    if str(root) not in sys.path:
        sys.path.insert(0, str(root))

    try:
        import loventre_meta_decision_engine as lmd
    except Exception as e:
        print("[ERROR] Impossibile importare loventre_meta_decision_engine:", e)
        print("sys.path attuale:")
        for p in sys.path:
            print("  -", p)
        sys.exit(1)

    if not hasattr(lmd, "_snapshot_loventre_core_baseline"):
        print("[ERROR] _snapshot_loventre_core_baseline non trovato nel meta–engine.")
        sys.exit(1)

    snapshot = lmd._snapshot_loventre_core_baseline  # type: ignore[attr-defined]

    def run_case(label: str, core_vals: dict) -> None:
        print("=" * 80)
        print(f"[{label}]")
        metrics = dict(core_vals)

        print("  --- Stato iniziale (prima dello snapshot) ---")
        for key in ["kappa_eff", "entropy_eff", "V0", "p_tunnel", "mass_mean", "chi", "risk_index"]:
            if key in metrics:
                print(f"   {key:12s} = {metrics[key]!r}")

        metrics = snapshot(metrics)

        print("\n  --- Dopo _snapshot_loventre_core_baseline ---")
        for key in ["kappa_eff", "entropy_eff", "V0", "p_tunnel", "mass_mean", "chi", "risk_index"]:
            base_key = f"{key}_base"
            print(
                f"   {key:12s} = {metrics.get(key)!r}   "
                f"{base_key:16s} = {metrics.get(base_key)!r}"
            )

        # Simuliamo una "deformazione" successiva dei valori correnti
        # come farebbero i layer fisici (Schwarzschild/Hawking/Planck).
        print("\n  --- Simulazione layer: deformiamo i valori correnti ---")
        if "kappa_eff" in metrics:
            metrics["kappa_eff"] = metrics["kappa_eff"] * 1.2
        if "entropy_eff" in metrics:
            metrics["entropy_eff"] = metrics["entropy_eff"] + 0.5
        if "risk_index" in metrics:
            metrics["risk_index"] = metrics["risk_index"] * 1.3

        for key in ["kappa_eff", "entropy_eff", "V0", "p_tunnel", "mass_mean", "chi", "risk_index"]:
            base_key = f"{key}_base"
            print(
                f"   {key:12s} = {metrics.get(key)!r}   "
                f"{base_key:16s} = {metrics.get(base_key)!r}"
            )

    print("=== LOVENTRE core baseline snapshot debug ===\n")

    cases = [
        (
            "CASE 1 – core moderato",
            {
                "kappa_eff": 0.7,
                "entropy_eff": 1.3,
                "V0": 2.0,
                "p_tunnel": 0.15,
                "mass_mean": 1.0,
                "chi": 0.25,
                "risk_index": 1.8,
            },
        ),
        (
            "CASE 2 – core più spinto",
            {
                "kappa_eff": 1.2,
                "entropy_eff": 2.5,
                "V0": 3.0,
                "p_tunnel": 0.35,
                "mass_mean": 1.7,
                "chi": 0.4,
                "risk_index": 3.2,
            },
        ),
    ]

    for label, core in cases:
        run_case(label, core)


if __name__ == "__main__":
    main()

