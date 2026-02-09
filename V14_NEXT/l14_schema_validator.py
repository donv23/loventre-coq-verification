"""
L14_SCHEMA_VALIDATOR — V14
==========================

Validatore minimale di struttura per l’export canonico.
Non verifica valori, solo presenza delle chiavi.

Funzione principale:
    validate_schema_v14(data_dict) -> True/False
"""

from V14_NEXT.l14_export_canon import EXPORT_SCHEMA_V14


def validate_schema_v14(data_dict):
    """
    Verifica che tutte le chiavi richieste dal template
    siano presenti nel dizionario passato.
    Ritorna True se valido, False altrimenti.
    """
    if not isinstance(data_dict, dict):
        return False
    for key in EXPORT_SCHEMA_V14.keys():
        if key not in data_dict:
            return False
    return True

