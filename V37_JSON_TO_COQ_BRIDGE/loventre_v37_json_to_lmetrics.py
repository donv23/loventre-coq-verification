"""
loventre_v37_json_to_lmetrics.py
Loventre Engine — V37 JSON → LMetrics translator (robust)
Gennaio 2026

Accetta 3 formati:
A) V36 flat  (trend=..., risk=..., prognosis=...)
B) V36 packed { "Classifier": {...}, "Prognosis": {...} }
C) V36 hybrid (trend string + embedded dicts)
"""

def _safe_upper(val):
    """
    Converte in upper solo se val è stringa.
    """
    if isinstance(val, str):
        return val.upper()
    return ""


def _is_packed(v36_dict):
    return ("Classifier" in v36_dict) or ("Prognosis" in v36_dict)


def _extract_flat(v36_dict):
    """
    Flat V36: trend/risk/prognosis sono stringhe top-level.
    """
    trend = _safe_upper(v36_dict.get("trend"))
    prognosis = _safe_upper(v36_dict.get("prognosis"))
    risk = _safe_upper(v36_dict.get("risk"))
    return trend, prognosis, risk, v36_dict


def _extract_packed(v36_dict):
    """
    Packed V36: blocchi embedded
    """
    cls = v36_dict.get("Classifier", {}) or {}
    prog = v36_dict.get("Prognosis", {}) or {}

    trend = _safe_upper(cls.get("trend") or prog.get("trend"))
    prognosis = _safe_upper(prog.get("prognosis"))
    risk = _safe_upper(prog.get("risk"))

    merged = {}
    merged.update(prog)
    merged.update(cls)
    return trend, prognosis, risk, merged


def _extract_hybrid(v36_dict):
    """
    Caso ibrido: campi top-level mescolati con dict embedded.
    """
    trend = _safe_upper(
        v36_dict.get("trend")
        or v36_dict.get("Classifier", {}).get("trend")
    )
    prognosis = _safe_upper(
        v36_dict.get("prognosis")
        or v36_dict.get("Prognosis", {}).get("prognosis")
    )
    risk = _safe_upper(
        v36_dict.get("risk")
        or v36_dict.get("Prognosis", {}).get("risk")
    )

    merged = {}
    for k in ("Classifier", "Prognosis"):
        if isinstance(v36_dict.get(k), dict):
            merged.update(v36_dict[k])

    # Se comunque vuoto, copia tutto
    if not merged:
        merged.update(v36_dict)
    return trend, prognosis, risk, merged


def json_to_lmetrics_v3(v36_dict):
    """
    Convertitore robusto V37.
    Tutti i campi non trovati sono 'UNKNOWN' o boolean False.
    """
    if _is_packed(v36_dict):
        trend, prognosis, risk, merged = _extract_packed(v36_dict)
    else:
        # verifica se i top-level non sono stringhe → hybrid
        top_trend = v36_dict.get("trend")
        if not isinstance(top_trend, str):
            trend, prognosis, risk, merged = _extract_hybrid(v36_dict)
        else:
            trend, prognosis, risk, merged = _extract_flat(v36_dict)

    # Classificazione grezza Loventre
    if trend == "STABLE":
        cls = "P_LIKE"
    elif trend == "OSCILLATING":
        cls = "P_ACCESSIBLE"
    else:
        cls = "NP_BH_LIKE"

    return {
        "loventre_class": cls,
        "trend_label": trend or "UNKNOWN",
        "risk_label": risk or "UNKNOWN",
        "prognosis_label": prognosis or "UNKNOWN",
        "instability_flag": bool(merged.get("instability_flag", False)),
        "recovery_flag": bool(merged.get("recovery_flag", False)),
        "advisory": merged.get("advisory"),
        "trend_counter": int(merged.get("trend_counter", 0)),
        "history_size": int(merged.get("history_size", 0)),
    }


def main():
    from loventre_v37_json_loader import load_v36_json
    import os

    root = "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/JSON_IO/V36_PROGNOSIS"
    files = sorted(f for f in os.listdir(root) if f.endswith(".json"))

    if not files:
        print("[V37 LMetrics] Nessun file V36 trovato.")
        return

    latest = os.path.join(root, files[-1])
    print(f"[V37 LMetrics] Carico: {latest}")
    data = load_v36_json(latest)
    lm = json_to_lmetrics_v3(data)
    print("[V37 LMetrics] LMetrics-like:", lm)


if __name__ == "__main__":
    main()

