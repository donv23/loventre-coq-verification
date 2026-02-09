"""
loventre_v35_classifier.py
Loventre Engine — V35 LONG MEMORY
Step 1: Classificatore finale di trend basato su stato V34
Gennaio 2026
"""

# Questo modulo prende il dict V34 e produce una sintesi strutturale.


def classify_final_trend(v34_summary: dict) -> dict:
    """
    Prende un output V34 (ultimo snapshot della storia)
    e restituisce un verdetto strutturale sintetico.

    Output di esempio:
    {
        "trend": "COLLAPSING",
        "instability_flag": True,
        "recovery_flag": False,
    }
    """

    # Default baseline
    result = {
        "trend": "UNKNOWN",
        "instability_flag": False,
        "recovery_flag": False,
    }

    if not isinstance(v34_summary, dict):
        result["trend"] = "INVALID_INPUT"
        result["instability_flag"] = True
        return result

    # Primo: identifichiamo la chiave primaria
    tag = v34_summary.get("trend_tag", None)
    counter = v34_summary.get("trend_counter", 0)
    emergency = v34_summary.get("emergency_lock", False)
    auto_damping = v34_summary.get("auto_damping", False)

    # LOGICA PRINCIPALE
    if tag is None:
        result["trend"] = "NO_DATA"
        return result

    # Caso 1 — Stabilità genuina
    if tag == "STABLE":
        result["trend"] = "STABLE"
        result["recovery_flag"] = True
        return result

    # Caso 2 — Oscillazione controllata ma evidente
    if tag == "OSCILLATING":
        result["trend"] = "OSCILLATING"
        result["instability_flag"] = True
        return result

    # Caso 3 — Deriva fuori controllo (segno di transizione sistematica)
    if tag == "DRIFTING":
        result["trend"] = "DRIFTING"
        result["instability_flag"] = True
        return result

    # Caso 4 — Tendenza al collasso (anche se input finale è SAFE)
    if tag == "COLLAPSING" or emergency:
        result["trend"] = "COLLAPSING"
        result["instability_flag"] = True
        return result

    # Catch-all per non perdere casi esperimentali
    result["trend"] = f"UNRECOGNIZED_{tag}"
    return result


def classify_with_history(v34_tail: list) -> dict:
    """
    Variante che accetta una LISTA di output V34 (storia recentissima)
    e classifica il trend sul penultimo o ultimo snapshot.

    Usata in future versioni V36+, qui per preparare la struttura.
    """

    if not isinstance(v34_tail, list) or len(v34_tail) == 0:
        return {
            "trend": "NO_HISTORY",
            "instability_flag": True,
            "recovery_flag": False,
        }

    # Per ora prendiamo l'ultimo
    latest = v34_tail[-1]
    base = classify_final_trend(latest)
    base["history_size"] = len(v34_tail)
    return base

