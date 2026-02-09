"""
loventre_witness_seeds.py
Witness ufficiali Python — v11 → v13
Allineati alla semantica Coq
"""

import json
from dataclasses import asdict

# Importa i layer fondamentali
from loventre_lmetrics_core import mkMetrics
from loventre_safe_layer import enforce_safe
from loventre_risk_class import classify
from loventre_classes import (
    is_P_like,
    is_P_accessible,
    is_NP_black_hole,
)

# (A) WITNESS BASE v11
m0 = mkMetrics(1)
m1 = enforce_safe(m0)

# (B) WITNESS P-accessible v12
m_Pacc_example = mkMetrics(1)

# (C) WITNESS NP-black-hole v13
m_NPbh_example = mkMetrics(3)

# (D) ASSERT — come i lemmi Coq
assert is_P_like(m1), "m1 dovrebbe essere P-like!"
assert is_P_accessible(m_Pacc_example), "m_Pacc_example deve essere P-accessible!"
assert not is_P_like(m_Pacc_example), "m_Pacc_example NON deve essere P-like!"
assert is_NP_black_hole(m_NPbh_example), "m_NPbh_example deve essere NP-black-hole!"

# (E) Micro pipeline di controllo
def pipeline_safe_only(m):
    """SAFE-only pipeline, come Coq v11–v13"""
    before = classify(m)
    after_safe = classify(enforce_safe(m))
    return before, after_safe

# (F) Utility: dump JSON
def dump_json(obj, name):
    with open(f"{name}.json", "w") as f:
        json.dump(asdict(obj), f, indent=2)

# (G) Report
def report():
    seeds = [
        ("m0", m0),
        ("m1", m1),
        ("m_Pacc_example", m_Pacc_example),
        ("m_NPbh_example", m_NPbh_example),
    ]
    print("=== WITNESS REPORT v11–v13 ===")
    for name, m in seeds:
        before, after = pipeline_safe_only(m)
        print(
            f"{name:16} | risk={m.risk_level:2} | "
            f"class={before:16} | SAFE→ {after:16}"
        )

# (H) JSON EXPORT automatico
dump_json(m0, "metrics_m0")
dump_json(m1, "metrics_m1")
dump_json(m_Pacc_example, "metrics_m_Pacc")
dump_json(m_NPbh_example, "metrics_m_NPbh")

if __name__ == "__main__":
    report()

