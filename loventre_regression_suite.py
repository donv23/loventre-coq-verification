"""
loventre_regression_suite.py

Regression suite minimale del Loventre Engine.
Estesa con guard morbido di robustezza strutturale (Robustness Stack v1).

Nessun FAIL automatico.
Solo WARN espliciti se la robustezza scende sotto soglia.
"""

from typing import Dict, Any

from loventre_meta_engine import loventre_collect_metrics_with_robustness


# =========================================================
# CONFIGURAZIONE GUARD ROBUSTEZZA
# =========================================================

ROBUST_MIN_LEVEL = 4   # livello minimo accettabile (structural)


# =========================================================
# RUN TEST
# =========================================================

def run_test(name: str, test_input: Dict[str, int]) -> None:
    try:
        print(f">>> TEST: {name}")

        metrics = loventre_collect_metrics_with_robustness(test_input)

        print("Result metrics:")
        for k in sorted(metrics.keys()):
            print(f"  {k}: {metrics[k]}")

        # -------------------------------
        # GUARD MORBIDO DI ROBUSTEZZA
        # -------------------------------
        level = metrics.get("robust_level")
        label = metrics.get("robust_label")

        if level is None:
            print("[WARN] Robustness Stack non presente nei metrics.")
        elif level < ROBUST_MIN_LEVEL:
            print(
                f"[WARN] Robustezza sotto soglia: "
                f"level={level}, label={label} (min={ROBUST_MIN_LEVEL})"
            )
        else:
            print(
                f"[OK] Robustezza strutturale OK: "
                f"level={level}, label={label}"
            )

    except Exception:
        import traceback
        print("[ENGINE ERROR]")
        print(traceback.format_exc())


# =========================================================
# ENTRY POINT MANUALE
# =========================================================

if __name__ == "__main__":
    # Test base canonico
    run_test("seed_(2,3)_canonical", {"param": 2, "factor": 3})

    # Test di controllo semplice
    run_test("seed_(1,1)_simple", {"param": 1, "factor": 1})

