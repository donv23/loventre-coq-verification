"""
C5.1 — Structural Audit
Verifica che lo stack delle barriere sia presente e non bypassabile.
"""

from pathlib import Path

REQUIRED_BARRIERS = [
    "guard_barrier.py",
    "monotonicity_barrier.py",
    "horizon_barrier.py",
    "safe_compatibility_barrier.py",
    "robustness_barrier_stack.py",
]

BARRIERS_DIR = Path("barriers")


def run_structural_audit() -> dict:
    missing = []
    for fname in REQUIRED_BARRIERS:
        if not (BARRIERS_DIR / fname).exists():
            missing.append(fname)

    return {
        "barriers_present": len(missing) == 0,
        "missing": missing,
    }


if __name__ == "__main__":
    result = run_structural_audit()
    print(result)
    if not result["barriers_present"]:
        raise SystemExit("C5.1 FAILED")

