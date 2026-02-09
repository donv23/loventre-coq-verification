"""
loventre_v41_rescue_mapper.py
Loventre Engine — V41 LMetrics Rescue Mapper
Gennaio 2026

Questo modulo prende un dizionario LMetrics potenzialmente incompleto
e tenta di ricostruire i campi minimi coerenti con il modello v3.
Mai sovrascrivere un campo valido; riempie solo i mancanti.
"""

REQUIRED = (
    "trend_label",
    "risk_label",
    "prognosis_label",
    "instability_flag",
    "recovery_flag",
)

DEFAULTS = {
    "trend_label": "UNKNOWN",
    "risk_label": "MEDIUM",
    "prognosis_label": "UNDEFINED",
    "instability_flag": True,
    "recovery_flag": False,
}


def rescue_lmetrics(raw_dict):
    """
    Ritorna una copia con tutti i campi REQUIRED garantiti.
    Non modifica i valori esistenti.
    """
    fixed = dict(raw_dict)

    for key in REQUIRED:
        if key not in fixed:
            fixed[key] = DEFAULTS[key]

    return fixed


def main():
    demo = {
        "trend_label": "STABLE"
        # altri campi mancanti...
    }
    print("[V41 Rescue Mapper] Input =", demo)
    print("[V41 Rescue Mapper] Output =", rescue_lmetrics(demo))


if __name__ == "__main__":
    main()

