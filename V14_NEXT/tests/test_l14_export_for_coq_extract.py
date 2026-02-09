"""
Test V19 — estrazione LMetrics
"""

from V14_NEXT.l14_export_for_coq import extract_lmetrics

def test_extract_lmetrics_basic():
    snap = {
        "state": "SAFE",
        "kappa_l1": 0.8,
        "entropy_eff": 0.5,
        "policy_dynamic": "STEADY",
        "version": "V14.2",
        "timestamp": "2026-01-10T12:00:00Z",
        "junk": "ignore me"
    }
    lm = extract_lmetrics(snap)
    assert set(lm.keys()) == {
        "state","kappa_l1","entropy_eff","policy","version","timestamp"
    }
    assert lm["policy"] == "STEADY"

