#!/usr/bin/env python3
"""
Debug macro–policy + Hawking UV:

- importa loventre_meta_decision_engine
- prova a usare apply_policy_bridge_to_metrics(metrics)
- se fallisce, applica direttamente:
    _compute_hawking_uv_risk_coupling
    _annotate_policy_with_hawking_uv

I casi sono sintetici: simuliamo un metrics in cui:
- risk_index è già calcolato
- le chiavi hawking_uv_* sono presenti
- esiste un policy_comment di base
"""

import sys
import pathlib


def main() -> None:
    # Aggancia la root del progetto
    root = pathlib.Path(__file__).resolve().parents[1]
    if str(root) not in sys.path:
        sys.path.insert(0, str(root))

    try:
        import loventre_meta_decision_engine as lmd
    except Exception as e:
        print("[ERROR] Impossibile importare loventre_meta_decision_engine:", e)
        print("sys.path:")
        for p in sys.path:
            print("  -", p)
        sys.exit(1)

    apply_bridge = getattr(lmd, "apply_policy_bridge_to_metrics", None)
    risk_helper = getattr(lmd, "_compute_hawking_uv_risk_coupling", None)
    uv_helper = getattr(lmd, "_annotate_policy_with_hawking_uv", None)

    if apply_bridge is None:
        print("[WARN] apply_policy_bridge_to_metrics non trovato.")
    if risk_helper is None:
        print("[WARN] _compute_hawking_uv_risk_coupling non trovato.")
    if uv_helper is None:
        print("[WARN] _annotate_policy_with_hawking_uv non trovato.")

    def run_case(label: str, seed_metrics: dict) -> None:
        print("=" * 80)
        print(f"[{label}]")

        metrics = dict(seed_metrics)

        def _apply_pipeline(m: dict) -> dict:
            # Tentiamo prima il Policy Bridge completo
            if apply_bridge is not None:
                try:
                    return apply_bridge(dict(m))
                except Exception as e:
                    print("  [INFO] apply_policy_bridge_to_metrics ha sollevato un'eccezione:", repr(e))
            # Fallback: applichiamo solo i due helper Hawking UV
            m2 = dict(m)
            if risk_helper is not None:
                try:
                    m2 = risk_helper(m2)
                except Exception as e:
                    print("  [INFO] risk_helper ha sollevato un'eccezione:", repr(e))
            if uv_helper is not None:
                try:
                    m2 = uv_helper(m2)
                except Exception as e:
                    print("  [INFO] uv_helper ha sollevato un'eccezione:", repr(e))
            return m2

        metrics = _apply_pipeline(metrics)

        # Stampa compatta dei campi interessanti
        def g(key, default=None):
            return metrics.get(key, default)

        print("  risk_index_hawking_base    =", g("risk_index_hawking_base"))
        print("  risk_index_hawking_coupled =", g("risk_index_hawking_coupled"))
        print("  risk_index_hawking_delta   =", g("risk_index_hawking_delta"))
        print("  risk_index (final)         =", g("risk_index"))
        print()
        print("  policy_strategy            =", g("policy_strategy"))
        print("  policy_energy              =", g("policy_energy"))
        print("  policy_uv_tag              =", g("policy_uv_tag"))
        print("  policy_uv_note             =", g("policy_uv_note"))
        print("  policy_uv_annotation       =", g("policy_uv_annotation"))
        print("  policy_comment:")
        print("   ", g("policy_comment"))
        print()
        print("  hawking_uv_phase           =", g("hawking_uv_phase"))
        print("  hawking_uv_index           =", g("hawking_uv_index"))
        print("  hawking_uv_energy          =", g("hawking_uv_energy"))

    print("=== LOVENTRE Policy Bridge + Hawking UV debug ===\n")

    cases = [
        (
            "CASE A – sub_uv quiet, policy neutra",
            {
                "risk_index": 1.0,
                "hawking_uv_phase": "sub_uv",
                "hawking_uv_index": 0.4,
                "hawking_uv_energy": 0.2,
                "policy_strategy": "neutral",
                "policy_energy": 0.5,
                "policy_comment": "policy base neutra su regime stazionario.",
            },
        ),
        (
            "CASE B – critical_uv edge, policy già prudente",
            {
                "risk_index": 2.0,
                "hawking_uv_phase": "critical_uv",
                "hawking_uv_index": 6.0,
                "hawking_uv_energy": 1.5,
                "policy_strategy": "cautious",
                "policy_energy": 0.8,
                "policy_comment": "policy già prudente su regime instabile.",
            },
        ),
        (
            "CASE C – trans_uv frontier, policy aggressiva",
            {
                "risk_index": 3.5,
                "hawking_uv_phase": "trans_uv",
                "hawking_uv_index": 15.0,
                "hawking_uv_energy": 3.0,
                "policy_strategy": "aggressive",
                "policy_energy": 1.2,
                "policy_comment": "policy aggressiva su confine di transizione.",
            },
        ),
    ]

    for label, seed in cases:
        run_case(label, seed)


if __name__ == "__main__":
    main()

