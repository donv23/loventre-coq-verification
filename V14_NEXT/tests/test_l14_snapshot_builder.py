"""
Test V14 — Snapshot Builder
===========================

Verifica che:
- build_v14_snapshot crea un dict valido
- copia correttamente i campi da un fake V13
- ignora campi extra
"""

from V14_NEXT.l14_snapshot_builder import build_v14_snapshot
from V14_NEXT.l14_schema_validator import validate_schema_v14
from V14_NEXT.l14_export_canon import get_export_template


def test_snapshot_basic():
    v13 = {
        "state": "SAFE",
        "kappa_l1": 0.7,
        "policy": "STEADY",
        "router_target": "LOCAL",
        "consistency_flag": "OK",
        "extra": "ignored"
    }
    snap = build_v14_snapshot(v13)
    assert validate_schema_v14(snap), "Snapshot deve rispettare schema"
    assert snap["state"] == "SAFE"
    assert snap["kappa_l1"] == 0.7
    assert snap["policy"] == "STEADY"
    assert snap["router_target"] == "LOCAL"
    assert snap["consistency_flag"] == "OK"


def test_snapshot_empty_input():
    snap = build_v14_snapshot(None)
    # deve restituire un template valido
    assert validate_schema_v14(snap), "Snapshot vuoto deve ancora rispettare schema"

