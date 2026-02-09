#!/usr/bin/env python3
# ============================================================
# LOVENTRE — PRE-CRITICAL STRESS TEST (ANTI-FALSE-POSITIVE)
# ============================================================
# - Sequenze NON monotone
# - Nessuna black hole finale
# - Verifica rientro del flag
# ============================================================

from typing import Dict, Any, List
from loventre_precritical_observer import detect_precritical_transition


def run_sequence(seq: List[Dict[str, Any]], label: str) -> None:
    print(f"\n=== STRESS SEQUENCE: {label} ===")

    prev = None
    for i, step in enumerate(seq):
        print(f"\n--- STEP {i} ---")
        for k, v in step.items():
            print(f"{k:28}: {v}")

        if prev is not None:
            report = detect_precritical_transition(prev, step)
            print("\n[Pre-critical observer]")
            for k, v in report.items():
                print(f"{k:28}: {v}")
        else:
            print("\n[Pre-critical observer] (no previous step)")

        prev = step


# ============================================================
# TEST SEQUENCES
# ============================================================

# 1️⃣ Oscillazione con rientro (NON critica)
sequence_recovery = [
    dict(chi_compactness=0.20, informational_potential=0.40, p_tunnel=0.80),
    dict(chi_compactness=0.35, informational_potential=0.65, p_tunnel=0.55),
    dict(chi_compactness=0.30, informational_potential=0.55, p_tunnel=0.65),
    dict(chi_compactness=0.28, informational_potential=0.50, p_tunnel=0.70),
]

# 2️⃣ Rumore strutturale (NO trend coerente)
sequence_noise = [
    dict(chi_compactness=0.22, informational_potential=0.42, p_tunnel=0.75),
    dict(chi_compactness=0.26, informational_potential=0.48, p_tunnel=0.72),
    dict(chi_compactness=0.24, informational_potential=0.45, p_tunnel=0.74),
    dict(chi_compactness=0.27, informational_potential=0.50, p_tunnel=0.70),
]

# 3️⃣ Crescita parziale che NON collassa
sequence_partial = [
    dict(chi_compactness=0.25, informational_potential=0.45, p_tunnel=0.70),
    dict(chi_compactness=0.38, informational_potential=0.70, p_tunnel=0.50),
    dict(chi_compactness=0.40, informational_potential=0.72, p_tunnel=0.52),
    dict(chi_compactness=0.37, informational_potential=0.68, p_tunnel=0.55),
]


if __name__ == "__main__":

    run_sequence(sequence_recovery, "Recovery after spike")
    run_sequence(sequence_noise, "Noisy oscillation")
    run_sequence(sequence_partial, "Partial growth without collapse")

