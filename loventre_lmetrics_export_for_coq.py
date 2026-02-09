#!/usr/bin/env python3
# loventre_lmetrics_export_for_coq.py
#
# Aggiunge il campo t_collapse_estimate a LMetrics JSON
# Versione V600 — minima e compatibile

import json
from pathlib import Path

def compute_t_collapse(kappa: float, entropy: float, V0: float):
    """
    Stima temporale grezza: alta curvatura + alta barriera → tempi brevi
    (placeholder lineare, raffinabile in V650+)
    """
    base = max(0.1, 10.0 - (kappa * 3.0 + V0 * 2.0 + entropy))
    return round(base, 3)

def export_with_time(input_json, output_json):
    data = json.loads(Path(input_json).read_text())

    kappa = data.get("kappa_eff", 0.0)
    entropy = data.get("entropy_eff", 0.0)
    V0 = data.get("V0", 0.0)

    t_est = compute_t_collapse(kappa, entropy, V0)
    data["t_collapse_estimate"] = t_est

    Path(output_json).write_text(json.dumps(data, indent=2))
    print(f"[V600] written → {output_json}")

if __name__ == "__main__":
    import sys
    if len(sys.argv) != 3:
        print("usage: python3 loventre_lmetrics_export_for_coq.py in.json out.json")
        sys.exit(1)

    export_with_time(sys.argv[1], sys.argv[2])

