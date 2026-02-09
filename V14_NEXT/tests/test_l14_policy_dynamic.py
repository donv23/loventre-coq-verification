"""
Test V18 — Policy dinamica
=========================
"""

from V14_NEXT.l14_policy_dynamic import compute_policy_dynamic

def test_policy_dynamic_fallback_no_history():
    snap = {"state": "SAFE", "policy": "DO_NOTHING"}
    p = compute_policy_dynamic(snap)
    assert p in ("DO_NOTHING", "STEADY", "EXPLORE_MORE")

