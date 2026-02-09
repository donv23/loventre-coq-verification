"""
loventre_v35_prognosis.py
Loventre Engine — V35 LONG MEMORY
Step 2: Traduzione trend → prognosi + advisory
Gennaio 2026
"""

from typing import Dict


def prognose_from_trend(trend_report: Dict) -> Dict:
    """
    Prende un classificatore V35 (produced by classify_final_trend)
    e aggiunge livello di rischio + prognosi + advisory.

    Esempio output:
    {
        "trend": "OSCILLATING",
        "risk": "MEDIUM",
        "prognosis": "UNSTABLE",
        "advisory": "Monitorare con attenzione; possibile transizione BH"
    }
    """

    # Setup baseline
    result = {
        "trend": trend_report.get("trend", "UNKNOWN"),
        "risk": "UNKNOWN",
        "prognosis": "UNKNOWN",
        "advisory": "Insufficient data.",
    }

    trend = trend_report.get("trend", None)
    unstable = trend_report.get("instability_flag", False)
    recovering = trend_report.get("recovery_flag", False)

    # CASO STABILE
    if trend == "STABLE":
        result["risk"] = "LOW"
        result["prognosis"] = "RECOVERING"
        result["advisory"] = "Condizione sana; proseguire rotta attuale."
        return result

    # OSCILLAZIONI
    if trend == "OSCILLATING":
        result["risk"] = "MEDIUM"
        result["prognosis"] = "UNSTABLE"
        result["advisory"] = "Oscillazioni rilevate; monitoraggio consigliato."
        return result

    # DERIVA
    if trend == "DRIFTING":
        result["risk"] = "MEDIUM"
        result["prognosis"] = "UNSTABLE"
        result["advisory"] = "Deriva strutturale; possibili transizioni di fase."
        return result

    # COLLASSO
    if trend == "COLLAPSING":
        result["risk"] = "HIGH"
        result["prognosis"] = "NEAR_BLACKHOLE"
        result["advisory"] = "Condizione critica; chiudere iterazioni o resettare parametri."
        return result

    # Tutti gli altri casi
    result["risk"] = "UNKNOWN"
    result["prognosis"] = "UNKNOWN"
    result["advisory"] = "Trend non riconosciuto; passare a debug."
    return result

