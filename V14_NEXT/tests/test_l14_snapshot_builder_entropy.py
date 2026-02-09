"""
Test V14 — Snapshot Builder + Entropy
=====================================

Verifica che entropy_eff appaia nel risultato.
"""

from V14_NEXT.l14_snapshot_builder import build_v14_snapshot

def test_snapshot_entropy_present():
    v13 = {
        "state": "SAFE",
        "kappa_l1": 0.9,
        "policy": "STEADY",
        "router_target": "LOCAL",
        "consistency_flag": "OK",
    }
    snap = build_v14_snapshot(v13)
    assert "entropy_eff" in snap
    assert snap["entropy_eff"] == 0.2

