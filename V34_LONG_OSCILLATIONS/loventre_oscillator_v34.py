"""
loventre_oscillator_v34.py
Loventre Engine — V34 Long-Horizon Oscillation tracker
Gennaio 2026

Questo modulo NON usa stati globali del motore.
Mantiene un buffer interno e interpreta pattern di oscillazione.
"""

from collections import deque
from typing import List, Dict, Tuple
from loventre_global_entrypoint import loventre_global_decide_with_policy


class OscillationTrackerV34:
    """
    Mantiene memoria breve e lunga degli ultimi output V33
    e produce metadati di oscillazione.
    """

    def __init__(self, memory_limit=8):
        self.memory_limit = memory_limit
        self.history = deque(maxlen=memory_limit)
        self.trend_counter = 0
        self.emergency_lock = False

    def feed(self, wrapped_state):
        """
        Aggiunge nuovo output V33 e aggiorna la diagnosi oscillazione.
        """
        # Registra il nuovo stato
        self.history.append(wrapped_state)

        # Estratti base
        kappa = wrapped_state.get("kappa_eff", 0.0)
        tag = wrapped_state.get("envelope_tag", "UNKNOWN")

        # Classificazione numerica envelope
        # SAFE_STRICT         → 0
        # SAFE_TUNNELED       → 1
        # BLACKHOLE_TRANSIENT → 2
        if tag == "SAFE_STRICT":
            score = 0
        elif tag == "SAFE_TUNNELED":
            score = 1
        elif tag == "BLACKHOLE_TRANSIENT":
            score = 2
        else:
            score = 1  # fallback intermedio

        # Conta BH_TRANSIENT nella finestra
        bh_recent = [1 for h in self.history if h.get("envelope_tag") == "BLACKHOLE_TRANSIENT"]
        if len(bh_recent) >= 2:
            self.emergency_lock = True

        # Calcolo drift qualitativo
        if len(self.history) >= 3:
            last = list(self.history)
            drift = score - (
                0.5 * (last[-2].get("kappa_eff", 0.0)) -
                0.5 * (last[-3].get("kappa_eff", 0.0))
            )
        else:
            drift = 0.0

        # Tag di tendenza
        if self.emergency_lock:
            trend_tag = "COLLAPSING"
            self.trend_counter += 1
        elif score == 0:
            trend_tag = "STABLE"
        elif score == 1:
            trend_tag = "DRIFTING"
        elif score == 2:
            trend_tag = "OSCILLATING"
        else:
            trend_tag = "UNKNOWN"

        # Restituisce lo stato V34
        return {
            "trend_tag": trend_tag,
            "trend_counter": self.trend_counter,
            "history_size": len(self.history),
            "auto_damping": (trend_tag in ("OSCILLATING", "COLLAPSING")),
            "emergency_lock": self.emergency_lock,
            "oscillation_score": score,
            "oscillation_drift": drift,
        }


def track_sequence_v34(params_list: List[Dict]) -> Tuple[list, list, list]:
    """
    Esegue una sequenza di parametri
    - chiama V33 (loventre_global_decide_with_policy)
    - applica l'envelope V33_SAFE
    - applica l'oscillation tracker V34
    restituisce tripletta:
    (raw_list, wrapped_list, v34_list)
    """

    tracker = OscillationTrackerV34()
    raw_list = []
    wrapped_list = []
    v34_list = []

    from V33_SAFE_ENVELOPE.loventre_safe_entrypoint_v33 import wrap_safe_envelope_v33

    for p in params_list:
        raw = loventre_global_decide_with_policy(**p)
        wrapped = wrap_safe_envelope_v33(raw)
        v34 = tracker.feed(wrapped)

        raw_list.append(raw)
        wrapped_list.append(wrapped)
        v34_list.append(v34)

    return raw_list, wrapped_list, v34_list

