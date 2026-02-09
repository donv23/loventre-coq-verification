"""
loventre_v36_entrypoint.py
Loventre Engine — V36 Export Demo
Gennaio 2026

Esegue:
- sequenza V33 → V34 (oscillator)
- diagnosi V35 (classifier + prognosis)
- salvataggio JSON V36
"""

from V34_LONG_OSCILLATIONS.loventre_oscillator_v34 import track_sequence_v34
from V35_LONG_MEMORY_PROGNOSIS.loventre_v35_classifier import classify_final_trend
from V35_LONG_MEMORY_PROGNOSIS.loventre_v35_prognosis import prognose_from_trend
from V36_LONG_MEMORY_EXPORT.loventre_v36_exporter import export_v36_prognosis


def main():
    print("\n===== LOVENTRE ENGINE — V36 MEMORY EXPORT DEMO =====\n")

    # Sequenza test identica a V35
    test_seq = [
        {"kappa_eff": 2.5},
        {"kappa_eff": 0.8},
        {"kappa_eff": -0.2},
        {"kappa_eff": 0.3},
        {"kappa_eff": -1.1},
        {"kappa_eff": 0.9},
        {"kappa_eff": -3.3},
        {"kappa_eff": 0.1},
    ]

    raw_list, wrapped_list, v34_list = track_sequence_v34(test_seq)

    final_state = v34_list[-1]

    classifier = classify_final_trend(final_state)
    prognosis = prognose_from_trend(classifier)

    print("--- FINAL STATE V35 ---")
    print("Classifier:", classifier)
    print("Prognosis:", prognosis)

    print("\n--- EXPORTING TO JSON (V36) ---")
    filepath = export_v36_prognosis(classifier, prognosis, extra={
        "final_v34_state": final_state,
        "history_count": len(v34_list),
    })

    print(f"Saved to: {filepath}")

    print("\n===== END V36 MEMORY EXPORT =====\n")


if __name__ == "__main__":
    main()

