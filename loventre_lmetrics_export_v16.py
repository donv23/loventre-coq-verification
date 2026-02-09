"""
loventre_lmetrics_export_v16.py — Export JSON dei witness canonici
"""

import json
import os

from loventre_lmetrics_core import mkMetrics
from loventre_safe_layer import enforce_safe
from loventre_risk_class import classify
from loventre_tunneling_v15 import tunneling_step

# Witness canonici
m0 = mkMetrics(1)
m1 = enforce_safe(m0)
m_Pacc_example = mkMetrics(1)
m_NPbh_example = mkMetrics(3)
m_tunnel_example = tunneling_step(m_NPbh_example)


def encode(m):
    return {
        "risk_level": m.risk_level,
        "class": classify(m)
    }

witnesses = {
    "m0": encode(m0),
    "m1": encode(m1),
    "m_Pacc_example": encode(m_Pacc_example),
    "m_NPbh_example": encode(m_NPbh_example),
    "m_tunnel_example": encode(m_tunnel_example)
}

OUTDIR = "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/JSON_IO/LMetrics_v2"

os.makedirs(OUTDIR, exist_ok=True)
outfile = os.path.join(OUTDIR, "loventre_lmetrics_witness_v16.json")

with open(outfile, "w") as f:
    json.dump(witnesses, f, indent=2)

print("Exported JSON →", outfile)

