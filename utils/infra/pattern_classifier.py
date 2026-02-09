"""
Algorithm C (seed v1.1) – Pattern classifier per Loventre Engine.

Combina:
- profilo 1D (regime della traiettoria scalare),
- profilo multicanale,
- spread locale dei channels nello stato,

per produrre un'etichetta di configurazione ad alto livello.
"""

from typing import Any, Dict, Optional

from flow_analyzer.core.state import State


def compute_channels_from_state(state: State) -> Dict[str, Any]:
    """
    Estrae dall'oggetto State:
    - gli ultimi 3 channels,
    - lo spread locale (max - min) su quei 3 valori.

    Se i channels non esistono, prova a usare gli ultimi 3 punti della history.
    Se non è possibile, restituisce None.
    """
    data = getattr(state, "data", {})
    if not isinstance(data, dict):
        return {"channels": None, "channels_spread": None}

    # Preferisci 'channels' se presenti (Modello B)
    channels = data.get("channels")
    history = data.get("history")

    tail: Optional[list] = None

    if isinstance(channels, list) and len(channels) >= 3:
        tail = channels[-3:]
    elif isinstance(history, list) and len(history) >= 3:
        tail = history[-3:]

    if tail is None:
        spread: Optional[float] = None
    else:
        try:
            spread = float(max(tail) - min(tail))
        except TypeError:
            spread = None

    return {"channels": tail, "channels_spread": spread}


def classify_configuration_label(
    regime_1d: str,
    regime_multichannel: str,
    channels_spread: Optional[float],
    local_small_threshold: float = 2.0,
    local_high_threshold: float = 5.0,
) -> str:
    """
    Restituisce un'etichetta grossolana di configurazione, combinando
    regime 1D, regime multicanale e spread locale dei channels.

    È volutamente euristica: è un "seed" per il lavoro teorico, non
    una tassonomia definitiva.
    """
    # Caso in cui non abbiamo info locali sufficienti
    if channels_spread is None:
        if regime_1d == "critical_high_entropy":
            return "critical_configuration_no_local_info"
        return "regular_or_intermediate_configuration_no_local_info"

    # 1) Regime critico pieno:
    #    - 1D critico
    #    - multicanale critico (high_spread)
    #    - spread locale grande
    if (
        regime_1d == "critical_high_entropy"
        and regime_multichannel in ("synchronized_high_spread", "desynchronized_high_spread")
        and channels_spread >= local_high_threshold
    ):
        return "fully_critical_configuration"

    # 2) Pre-criticità geometrica:
    #    - 1D NON ancora critical_high_entropy
    #    - multicanale già high_spread
    #    - spread locale non banale
    if (
        regime_1d != "critical_high_entropy"
        and regime_multichannel in ("synchronized_high_spread", "desynchronized_high_spread")
        and channels_spread > local_small_threshold
    ):
        return "geometric_precritical_configuration"

    # 3) Regime regolare:
    #    - 1D non critico
    #    - multicanale sincronizzato o misto ma non high_spread
    #    - spread locale molto piccolo
    if (
        regime_multichannel in ("synchronized_low_spread", "mixed_intermediate")
        and channels_spread <= local_small_threshold
        and regime_1d != "critical_high_entropy"
    ):
        return "regular_configuration"

    # 4) Caso misto / non classificato in modo più preciso
    return "mixed_configuration"


def analyze_configuration_pattern(
    state: State,
    profile_1d: Dict[str, Any],
    multichannel_profile: Dict[str, Any],
    local_small_threshold: float = 2.0,
    local_high_threshold: float = 5.0,
) -> Dict[str, Any]:
    """
    Algoritmo C (seed v1.1): combina le tre sorgenti di informazione
    in un unico profilo di configurazione.
    """
    # Regimi 1D e multicanale
    regime_1d = profile_1d.get("regime", "unknown")
    regime_multichannel = multichannel_profile.get("regime_multichannel", "unknown")

    # Informazione locale dallo stato (channels e spread)
    channels_info = compute_channels_from_state(state)
    channels = channels_info["channels"]
    channels_spread = channels_info["channels_spread"]

    # Etichetta principale
    configuration_label = classify_configuration_label(
        regime_1d=regime_1d,
        regime_multichannel=regime_multichannel,
        channels_spread=channels_spread,
        local_small_threshold=local_small_threshold,
        local_high_threshold=local_high_threshold,
    )

    # Flag di comodo
    is_fully_critical = configuration_label == "fully_critical_configuration"
    has_geometric_precriticality = configuration_label == "geometric_precritical_configuration"
    is_regular = configuration_label == "regular_configuration"

    return {
        "configuration_label": configuration_label,
        "regime_1d": regime_1d,
        "regime_multichannel": regime_multichannel,
        "channels": channels,
        "channels_spread": channels_spread,
        "flags": {
            "is_fully_critical": is_fully_critical,
            "has_geometric_precriticality": has_geometric_precriticality,
            "is_regular": is_regular,
        },
    }


if __name__ == "__main__":
    # Mini self-test giusto per verificare che il modulo gira da solo.
    from pprint import pprint

    # Caso tipo fully-critical: 1D critico, multicanale high_spread, spread >= 5
    dummy_profile_1d = {"regime": "critical_high_entropy"}
    dummy_multi = {"regime_multichannel": "synchronized_high_spread"}

    class DummyState:
        def __init__(self):
            self.data = {"channels": [10, 20, 100]}  # spread = 90

    s = DummyState()
    result = analyze_configuration_pattern(
        state=s,
        profile_1d=dummy_profile_1d,
        multichannel_profile=dummy_multi,
    )
    pprint(result)

