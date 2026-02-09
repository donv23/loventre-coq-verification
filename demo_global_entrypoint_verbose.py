#!/usr/bin/env python3
"""
demo_global_entrypoint_verbose.py
Loventre Engine — V6 Global Verbose Entrypoint

Versione diagnostica estesa:
 - Stampa decisione SAFE/BLACKHOLE
 - Mostra colore e score
 - Mostra kappa, entropy, inertia
 - Mostra risk_class con soglie dinamiche
 - Stampa policy_hints e reason
 - Evidenzia terminal regime (BLACKHOLE)
 - Mostra meta_label e global_meta_explanation

Gennaio 2026 — Demo Verbose
"""

from policy.loventre_meta_decision_engine import meta_decide_instance_with_mass_global

def run_case(kappa=None, entropy=None):
    metrics = {}
    if kappa is not None:
        metrics["kappa_eff"] = kappa
    if entropy is not None:
        metrics["entropy_eff"] = entropy

    out = meta_decide_instance_with_mass_global(**metrics)

    lg = out["loventre_global"]
    pol = out.get("policy_hints", {})
    meta_reason = out.get("global_meta_explanation", "")
    meta_label = out.get("meta_label", "n/a")

    print(
        f"  decision={lg['global_decision']:<11}"
        f" color={lg['global_color']:<5}"
        f" score={lg['global_score']:<3} "
        f"kappa={out['kappa_eff']:>4} "
        f"entropy={str(out.get('entropy_eff')):<5} "
        f"inertia={out.get('inertial_idx', 0):<4} "
        f"risk={out.get('risk_class','?')}"
    )
    print(f"    policy_hint: {pol.get('reason','n/a')}")
    if pol.get("terminal_regime", False):
        print("    ⚠ TERMINAL REGIME / NO RECOVERY")
    print(f"    meta_label: {meta_label}")
    print(f"    meta_explanation: {meta_reason}")
    print()


def main():
    print("\n===== LOVENTRE ENGINE — GLOBAL ENTRYPOINT V6 (VERBOSE) =====\n")

    kappas = [3.0, 1.0, 0.3, 0.0, -0.1, -0.6, -2.0]
    entropies = [None, 1.0, 4.0]

    total = 0
    for ent in entropies:
        print("---------------------------------------------")
        print(f" ENTROPY = {ent}")
        print("---------------------------------------------")
        for k in kappas:
            run_case(k, ent)
            total += 1

    print(f"===== END GLOBAL ENTRYPOINT V6 VERBOSE — {total} casi analizzati =====")

if __name__ == "__main__":
    main()

