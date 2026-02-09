"""
loventre_v40_cleaner.py
Loventre Engine — V40 Cleaner
Gennaio 2026

Tenta di "ripulire" un dict LMetrics-like:

- Mantiene SOLO i campi dello schema minimo.
- Se un campo manca -> fallisce rumorosamente (ritorna None).
"""

from loventre_v40_validator import REQUIRED_KEYS


def clean_lmetrics(lmetrics_dict):
    """
    Restituisce un nuovo dict contenente SOLO le chiavi richieste.
    Se una chiave è assente -> ritorna None.
    """
    new_dict = {}
    for key in REQUIRED_KEYS:
        if key not in lmetrics_dict:
            return None
        new_dict[key] = lmetrics_dict[key]
    return new_dict

