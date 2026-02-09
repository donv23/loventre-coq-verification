"""
Test V14 — Export Template
==========================

Controlla che:
- get_export_template() esista
- ritorni un dict
- contenga tutte le chiavi dello schema canonico
- abbia version uguale a VERSION_TAG
- non abbia side-effects su chiamate ripetute
"""

from V14_NEXT.l14_export_canon import (
    get_export_template,
    EXPORT_SCHEMA_V14,
    VERSION_TAG,
)


def test_l14_export_template_basic():
    temp = get_export_template()
    assert isinstance(temp, dict), "Template deve essere un dict"


def test_l14_export_template_keys():
    temp = get_export_template()
    for k in EXPORT_SCHEMA_V14.keys():
        assert k in temp, f"Key mancante nel template: {k}"


def test_l14_export_template_version():
    temp = get_export_template()
    assert temp["version"] == VERSION_TAG, "Version non corretta"


def test_l14_export_template_fresh_copy():
    a = get_export_template()
    b = get_export_template()
    assert a is not b, "Due template devono essere istanze separate"
    assert a == b, "Due template devono essere uguali nel contenuto"

