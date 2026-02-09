"""
loventre_v39_probe.py
Loventre Engine — V39 JSON → Coq Probe
Gennaio 2026

Questo modulo:
  • Carica un file LMetrics-ready V38 (JSON)
  • Estrae i campi chiave se presenti
  • Segnala i campi mancanti
  • NON modifica, NON converte, NON valida
"""

import json
import os


EXPECTED_KEYS = [
    "trend_label",
    "risk_label",
    "prognosis_label",
    "instability_flag",
    "recovery_flag",
]


def probe_lmetrics_dict(d):
    """
    Prova l'LMetrics dict e ritorna un report minimale.
    Campi assenti vengono segnalati come 'MISSING'.
    """
    report = {}

    for key in EXPECTED_KEYS:
        if key in d:
            report[key] = d[key]
        else:
            report[key] = "MISSING"

    # metadato opzionale solo informativo
    report["raw_keys_present"] = sorted(list(d.keys()))

    return report

