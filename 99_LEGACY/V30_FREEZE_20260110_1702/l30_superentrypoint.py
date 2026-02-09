"""
V30 SUPERENTRYPOINT — versione stabile

Coordina:
- pipeline V14 dinamica
- detector cicli (V23)
- classifier trend (V21)
- restituisce un super-snapshot globale
"""

from V14_NEXT.l14_export_act_dynamic import run_export_l14_dynamic
from V21_NEXT.l21_trend_classifier import classify_trend
from V23_NEXT.l23_cycle_detector import detect_cycle


def run_superentrypoint_v30(raw_value=0.5):
    """
    Esegue l’intero ciclo:
    1. Avvia pipeline V14 con policy dinamica
    2. Classifica trend storico
    3. Rileva cicli
    4. Ritorna un dizionario compatto
    """

    # 1. export dinamico (e memoria aggiornata)
    ok = run_export_l14_dynamic(raw_value)

    # 2. trend macro (stable / explore / collapse / unknown)
    trend = classify_trend(window=30)

    # 3. ciclo micro (stable_return / switching / drifting / unknown)
    cycle = detect_cycle(window=60)

    return {
        "ok": ok,
        "trend": trend,
        "cycle": cycle,
        "raw_value": raw_value,
    }

