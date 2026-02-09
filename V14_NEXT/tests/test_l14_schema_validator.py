"""
Test V14 — Schema Validator
===========================

Verifica che:
- validate_schema_v14 ritorni True per un template valido
- ritorni False se manca una chiave
- ritorni False se input non è dict
"""

from V14_NEXT.l14_export_canon import get_export_template
from V14_NEXT.l14_schema_validator import validate_schema_v14


def test_schema_ok():
    t = get_export_template()
    assert validate_schema_v14(t), "Template valido deve passare"


def test_schema_missing_key():
    t = get_export_template()
    t.pop("state")
    assert not validate_schema_v14(t), "Schema con key mancante deve fallire"


def test_schema_wrong_type():
    assert not validate_schema_v14(None), "None non è schema valido"
    assert not validate_schema_v14([]), "Lista non valida"

