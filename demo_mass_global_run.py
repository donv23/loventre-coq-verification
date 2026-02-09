"""
demo_mass_global_run.py
Loventre Engine – V6 Mass Demo
Gennaio 2026
"""

from pprint import pprint
from loventre_global_entrypoint import loventre_global_decide_with_policy

PRINT_SEP = "=" * 80

def run_case(label, **kwargs):
    print(PRINT_SEP)
    print(f"CASE: {label}")
    out = loventre_global_decide_with_policy(**kwargs)
    pprint(out)
    return out

def main():
    print("\n===== LOVENTRE ENGINE – MASS LAYER V6 DEMO =====\n")

    # Default
    run_case("default (no kappa)")

    # SAFE side small
    run_case("SAFE (kappa=+0.3)", kappa_eff=+0.3)

    # SAFE strong
    run_case("SAFE (kappa=+2.0)", kappa_eff=+2.0)

    # BLACKHOLE light
    run_case("BLACKHOLE (kappa=-0.7)", kappa_eff=-0.7)

    # BLACKHOLE deep
    run_case("BLACKHOLE (kappa=-2.5)", kappa_eff=-2.5)

    # Entropy-only (no kappa)
    run_case("ENTROPY ONLY (entropy=5.0)", entropy_eff=5.0)

    print("\n===== END MASS V6 DEMO =====\n")

if __name__ == "__main__":
    main()

