"""
loventre_v35_entrypoint.py
Loventre Engine — V35 LONG MEMORY: Verdict Unico
Step finale corretto — chiama loventre_global_decide_with_policy
Gennaio 2026
"""

from loventre_global_entrypoint import loventre_global_decide_with_policy
from V33_SAFE_ENVELOPE.loventre_safe_envelope_v33 import interpret_with_envelope
from V34_LONG_OSCILLATIONS.loventre_oscillator_v34 import OscillationTrackerV34
from V35_LONG_MEMORY_PROGNOSIS.loventre_v35_classifier import classify_final_trend
from V35_LONG_MEMORY_PROGNOSIS.loventre_v35_prognosis import prognose_from_trend


def main():
    print("\n===== LOVENTRE ENGINE — V35 LONG MEMORY VERDICT =====\n")

    tracker = OscillationTrackerV34()

    # Sequenza di prova V6 usata in V34
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

    last_v34 = None

    for idx, params in enumerate(inputs):
        print("=" * 80)
        print(f"CASE {idx+1}: {params}")

        # RAW V6 diretto
        raw = loventre_global_decide_with_policy(**params)
        print(" RAW:", raw)

        # V33
        v33 = interpret_with_envelope(raw)
        print(" V33:", v33)

        # V34
        v34 = tracker.feed(v33)
        print(" V34:", v34)

        last_v34 = v34

    print("\n--- V35 FINAL SYNTHESIS ---")

    # V35 — classifier
    summary = classify_final_trend(last_v34)
    print("Classifier:", summary)

    # V35 — prognosis + advisory
    decision = prognose_from_trend(summary)
    print("Prognosis:", decision)

    print("\n===== END V35 LONG MEMORY VERDICT =====\n")


if __name__ == "__main__":
    main()

