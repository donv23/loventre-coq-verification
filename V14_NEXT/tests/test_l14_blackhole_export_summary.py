"""
Test V20 — export lemma JSON
"""

import os
from V14_NEXT.l14_blackhole_export_summary import run_export_blackhole_summary_v20, EXPORT_DIR

def test_export_blackhole_summary():
    ok = run_export_blackhole_summary_v20(num_steps=20)
    assert ok
    assert "blackhole_non_risalita_summary.json" in os.listdir(EXPORT_DIR)

