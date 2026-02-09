"""
loventre_oscillation_entrypoint_v34.py
Loventre Engine — V34 Oscillation-aware execution
Gennaio 2026

Sequenza di passaggi:
  V6  → valutazione grezza
  V33 → SAFE envelope e mitigazione
  V34 → rilevazione oscillazioni & controllo meta
"""

from loventre_global_entrypoint import loventre_global_decide_with_policy
from V33_SAFE_ENVELOPE.loventre_safe_envelope_v33 import interpret_with_envelope
from V34_LONG_OSCILLATIONS.loventre_oscillator_v34 import OscillationTrackerV34


def v34_sweep_cases():
    """
    Lista oscillante volutamente non monotona.
    Spinge il motore dentro e fuori le classi critiche.
    """
    return [
        ("+2.5", {"kappa_eff": 2.5}),
        ("+0.8", {"kappa_eff": 0.8}),
        ("-0.2", {"kappa_eff": -0.2}),
        ("+0.3", {"kappa_eff": 0.3}),
        ("-1.1", {"kappa_eff": -1.1}),
        ("+0.9", {"kappa_eff": 0.9}),
        ("-3.3", {"kappa_eff": -3.3}),
        ("+0.1", {"kappa_eff": 0.1}),
    ]


def main():
    print("\n===== LOVENTRE ENGINE — V34 LONG-HORIZON OSCILLATIONS =====\n")

    tracker = OscillationTrackerV34()
    cases = v34_sweep_cases()

    for label, kwargs in cases:
        raw = loventre_global_decide_with_policy(**kwargs)
        wrapped = interpret_with_envelope(raw)
        osc = tracker.feed(wrapped)

        print("=" * 80)
        print(f"CASE: {label}")
        print(f" RAW: {raw}")
        print(f" V33: {wrapped}")
        print(f" V34: {osc}")

    print("\n===== END V34 LONG-HORIZON OSCILLATIONS =====\n")


if __name__ == "__main__":
    main()

