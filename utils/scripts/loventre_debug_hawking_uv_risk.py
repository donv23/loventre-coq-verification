#!/usr/bin/env python3
"""
Mini debug per il canale Hawking UV ↔ risk_index.

Non modifica nessun file core:
- importa loventre_meta_decision_engine (aggiungendo la root al sys.path)
- usa _compute_hawking_uv_risk_coupling(metrics) su alcuni casi sintetici
- stampa la deformazione del risk_index dovuta al canale Hawking UV.
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
        print(" sys.path attuale:")
        for p in sys.path:
            print("  -", p)
        sys.exit(1)

    if not hasattr(lmd, "_compute_hawking_uv_risk_coupling"):
        print("[ERROR] _compute_hawking_uv_risk_coupling non trovato nel meta–engine.")
        sys.exit(1)

    compute = lmd._compute_hawking_uv_risk_coupling  # type: ignore[attr-defined]

    def debug_case(label: str, base_risk: float, uv_index: float, uv_phase: str, uv_energy: float) -> None:
        metrics = {
            "risk_index": base_risk,
            "hawking_uv_index": uv_index,
            "hawking_uv_phase": uv_phase,
            "hawking_uv_energy": uv_energy,
        }
        metrics = compute(metrics)

        # Preparazione valori safe per stampa
        def _as_float(x, default=0.0) -> float:
            try:
                return float(x)
            except Exception:
                return float(default)

        uv_idx_disp = _as_float(metrics.get("hawking_uv_index", uv_index))
        uv_energy_disp = _as_float(metrics.get("hawking_uv_energy", uv_energy))

        print("=" * 72)
        print(f"[{label}]")
        print(
            f"  phase = {metrics.get('hawking_uv_phase')!r}  "
            f"uv_index ≈ {uv_idx_disp:.4f}  "
            f"uv_energy ≈ {uv_energy_disp:.4f}"
        )
        print(f"  risk_index_hawking_base    = {metrics.get('risk_index_hawking_base')}")
        print(f"  risk_index_hawking_coupled = {metrics.get('risk_index_hawking_coupled')}")
        print(f"  risk_index_hawking_delta   = {metrics.get('risk_index_hawking_delta')}")
        print(f"  risk_index (final)         = {metrics.get('risk_index')}")
        print("  hawking_uv_risk_comment:")
        print("   ", metrics.get("hawking_uv_risk_comment"))

    print("=== LOVENTRE Hawking UV ↔ risk_index debug ===")
    print("Tutti i casi sono sintetici, con metriche costruite a mano.\n")

    # Casi di test: base_risk fisso, varie fasi UV e intensità
    cases = [
        # base_risk, uv_index, uv_phase,      uv_energy, label
        (1.0, 0.5,  "sub_uv",      0.3,  "CASE 1 – sub_uv, UV basso"),
        (1.0, 5.0,  "critical_uv", 1.0,  "CASE 2 – critical_uv, UV medio"),
        (1.0, 20.0, "trans_uv",    3.0,  "CASE 3 – trans_uv, UV alto"),
        (5.0, 10.0, "sub_uv",      2.0,  "CASE 4 – sub_uv, rischio base alto"),
        (5.0, 10.0, "trans_uv",    2.0,  "CASE 5 – trans_uv, rischio base alto"),
        (2.0, 0.0,  "unknown",     0.0,  "CASE 6 – fase sconosciuta (neutro)"),
    ]

    for base_risk, uv_idx, phase, energy, label in cases:
        debug_case(label, base_risk, uv_idx, phase, energy)


if __name__ == "__main__":
    main()

