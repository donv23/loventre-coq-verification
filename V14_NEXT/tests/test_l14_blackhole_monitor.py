"""
Test V20 — monitor non-risalita
Only checks structure, not truth of lemma.
"""

from V14_NEXT.l14_blackhole_monitor import run_sequence_v20

def test_monitor_runs():
    res = run_sequence_v20(num_steps=10)
    assert "trace" in res
    assert "num_steps" in res
    assert len(res["trace"]) > 0

