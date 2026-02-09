"""
V23 — Season Classifier
Mappa il comportamento ciclico in macro-stagioni informazionali.
"""

from .l23_cycle_detector import detect_cycle

def classify_season(window=100):
    """
    Ritorna una stagione metaforica:
    - 'spring'   → switching / espansione
    - 'summer'   → stable_return / produttivo
    - 'autumn'   → drifting / instabile
    - 'winter'   → collasso percepito / blackhole-rich
    - 'unknown'
    """
    phase = detect_cycle(window)

    if phase == "stable_return":
        return "summer"
    if phase == "switching":
        return "spring"
    if phase == "drifting":
        return "autumn"

    # deduzione debole per winter: memoria scura
    # blackhole potrebbe essere rilevato indirettamente
    if phase in ("unknown",):
        return "winter"

    return "unknown"

