"""
C5.2 — Invariant Witness Check
Controlla che il tipo finale sia ammesso.
"""

ALLOWED_TYPES = {"P_STR", "P_ACC", "BH_NP"}


class C5InvariantError(Exception):
    pass


def check_invariants(final_metrics: dict) -> dict:
    t = final_metrics.get("LMetrics_type")

    violations = []
    if t not in ALLOWED_TYPES:
        violations.append(f"Invalid LMetrics_type: {t}")

    ok = len(violations) == 0

    return {
        "invariants_ok": ok,
        "violations": violations,
    }


if __name__ == "__main__":
    # smoke minimale
    test = {"LMetrics_type": "P_STR"}
    print(check_invariants(test))

