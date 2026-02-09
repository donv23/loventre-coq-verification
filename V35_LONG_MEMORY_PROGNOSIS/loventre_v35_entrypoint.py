"""
loventre_v35_entrypoint.py
Loventre Engine — V35 LONG MEMORY: Verdict Unico
Step 3 corretto — usa track_sequence_v34 invece della classe OscillationTracker
Gennaio 2026
"""

from demo_seed_global_decision import run_case as run_seed_raw
from V33_SAFE_ENVELOPE.loventre_safe_envelope_v33 import interpret_with_envelope
from V34_LONG_OSCILLATIONS.loventre_oscillator_v34 import track_sequence_v34
from V35_LONG_MEMORY_PROGNOSIS.loventre_v35_classifier import classify_final_trend
from V35_LONG_MEMORY_PROGNOSIS.loventre_v35_prognosis import prognose_from_trend


def main():
    print("\n===== LOVENTRE ENGINE — V35 LONG MEMORY VERDICT =====\n")

    # Sequenza presa come base V34
    inputs = [
        {"kappa_eff": +2.5},
        {"kappa_eff": +0.8},
        {"kappa_eff": -0.2},
        {"kappa_eff": +0.3},
        {"kappa_eff": -1.1},
        {"kappa_eff": +0.9},
        {"kappa_eff": -3.3},
        {"kappa_eff": +0.1},
    ]

    v33_outputs = []

    for idx, params in enumerate(inputs):
        label = f"CASE {idx+1} {params}"
        print("=" * 80)
        print(label)

        # RAW V6
        raw = run_seed_raw.__wrapped__(**params)

        # V33 safetization
        v33 = interpret_with_envelope(raw)
        print(" V33:", v33)

        v33_outputs.append(v33)

    print("\n--- V35 FINAL SYNTHESIS ---")

    # V34 — compute oscillation summary
    v34_summary = track_sequence_v34(v33_outputs)
    print("V34 summary:", v34_summary)

    # V35 — classifier
    summary = classify_final_trend(v34_summary)
    print("Classifier:", summary)

    # V35 — prognosis
    decision = prognose_from_trend(summary)
    print("Prognosis:", decision)

    print("\n===== END V35 LONG MEMORY VERDICT =====\n")


if __name__ == "__main__":
    main()

