"""
V30_NEXT/tests/test_l30_superentrypoint.py
Test base per Superentrypoint V30.
"""

from V30_NEXT.l30_superentrypoint import run_superentrypoint_v30


def test_v30_superentrypoint():
    snap = run_superentrypoint_v30(0.3, [0.3, 0.4, 0.25, 0.38])

    assert isinstance(snap, dict)
    assert snap.get("version") == "V30"

    expected_keys = [
        "seed_input",
        "core_state",
        "dynamic_action",
        "trend",
        "transition_counts",
        "cycle_detected",
        "season",
        "memory_top",
        "memory_pruned",
        "policy_history",
        "policy_feedback",
        "self_tuning",
        "throttle",
        "risk_resonance",
    ]

    for k in expected_keys:
        assert k in snap, f"Manca chiave {k}"

    print("✔ V30 SUPERENTRYPOINT OK")

