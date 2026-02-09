"""
loventre_v40_validator.py
Loventre Engine — V40 Strict Validator
Gennaio 2026

Controlla che un oggetto LMetrics-like soddisfi
lo schema minimo richiesto per la pipeline Coq v3+.

Schema obbligatorio:

trend_label       (str)
risk_label        (str)
prognosis_label   (str)
instability_flag  (bool)
recovery_flag     (bool)
"""

REQUIRED_KEYS = [
    "trend_label",
    "risk_label",
    "prognosis_label",
    "instability_flag",
    "recovery_flag",
]


def validate_lmetrics(lmetrics_dict):
    """
    Verifica che il dict fornito rispetti lo schema richiesto.

    Ritorna:
      (True, [])                se valido
      (False, [error1, ...])    se mancano chiavi o tipi incompatibili
    """
    errors = []

    # 1. Check presenza chiavi
    for key in REQUIRED_KEYS:
        if key not in lmetrics_dict:
            errors.append(f"Missing required field: {key}")

    if errors:
        return False, errors

    # 2. Check tipi minimi
    if not isinstance(lmetrics_dict.get("trend_label"), str):
        errors.append("trend_label must be string")
    if not isinstance(lmetrics_dict.get("risk_label"), str):
        errors.append("risk_label must be string")
    if not isinstance(lmetrics_dict.get("prognosis_label"), str):
        errors.append("prognosis_label must be string")
    if not isinstance(lmetrics_dict.get("instability_flag"), bool):
        errors.append("instability_flag must be bool")
    if not isinstance(lmetrics_dict.get("recovery_flag"), bool):
        errors.append("recovery_flag must be bool")

    return (len(errors) == 0), errors

