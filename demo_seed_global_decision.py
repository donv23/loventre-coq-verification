"""
demo_seed_global_decision.py
Loventre Engine — V6 seed-based global decision demo
Gennaio 2026
"""

from loventre_global_entrypoint import loventre_global_decide_with_policy


def run_case(label, **kwargs):
    print("=" * 80)
    print(f"CASE: {label}")
    out = loventre_global_decide_with_policy(**kwargs)
    print(out)


def main():
    print("\n===== LOVENTRE ENGINE – SEED GLOBAL DECISION V6 DEMO =====\n")

    # Nessun parametro → default SAFE
    run_case("default (no kappa)")

    # SAFE
    run_case("SAFE (+0.1)", kappa_eff=0.1)
    run_case("SAFE (+0.8)", kappa_eff=0.8)
    run_case("SAFE (+2.5)", kappa_eff=2.5)

    # BLACKHOLE
    run_case("BLACKHOLE (-0.2)", kappa_eff=-0.2)
    run_case("BLACKHOLE (-1.1)", kappa_eff=-1.1)
    run_case("BLACKHOLE (-3.3)", kappa_eff=-3.3)

    # Entropia senza kappa
    run_case("PARTIAL (entropy only=4.0)", entropy_eff=4.0)

    print("\n===== END SEED GLOBAL DECISION V6 DEMO =====\n")


if __name__ == "__main__":
    main()

