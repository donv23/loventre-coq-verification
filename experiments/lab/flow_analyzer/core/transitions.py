from typing import Callable, Any, Dict, List

from .state import State


def apply_transition(state: State, transition: Callable[[State], State]) -> State:
    """
    Adapter usato dal FlowEngine.

    Il FlowEngine chiama:
        new_state = apply_transition(current_state, transition)

    In questa versione seed, i transition sono funzioni State -> State,
    quindi qui controlliamo solo che siano chiamabili e li applichiamo.
    """
    if not callable(transition):
        raise TypeError("transition must be callable")
    return transition(state)


def _get_history(data: Dict[str, Any]) -> List[float]:
    """Recupera la history in modo sicuro da data."""
    history = data.get("history", [])
    if not isinstance(history, list):
        return []
    return history


def _update_channels_from_history(history: List[float], size: int = 3) -> List[float]:
    """
    Costruisce il vettore 'channels' a partire dalla history.

    Per il Modello B (seed) scegliamo:
    - channels = ultimi 'size' valori della history (se disponibili),
    - se la history è più corta, ripetiamo l'ultimo valore a sinistra.
    """
    if not history:
        return [0.0] * size

    if len(history) >= size:
        window = history[-size:]
    else:
        last = history[-1]
        pad_len = size - len(history)
        window = [last] * pad_len + history

    return window


def apply_algorithm_a(param: float) -> Callable[[State], State]:
    """
    Primo algoritmo (A): aggiorna value, history e channels.

    new_value   = value + param
    new_history = history + [new_value]
    channels    = ultimi 3 valori della history aggiornata
    """
    def transition(state: State) -> State:
        base_data = getattr(state, "data", {})
        if not isinstance(base_data, dict):
            base_data = {}

        # Copia per non modificare in-place
        data: Dict[str, Any] = dict(base_data)

        value = data.get("value", 0)
        history = _get_history(data)

        # Nuovo value e nuova history
        new_value = value + param
        new_history = history + [new_value]

        # Aggiorna campi dello stato
        data["value"] = new_value
        data["history"] = new_history
        data["channels"] = _update_channels_from_history(new_history, size=3)

        return State(data=data)

    return transition


def apply_algorithm_b(factor: float) -> Callable[[State], State]:
    """
    Secondo algoritmo (B): aggiorna value, history e channels.

    new_value   = value * factor
    new_history = history + [new_value]
    channels    = ultimi 3 valori della history aggiornata
    """
    def transition(state: State) -> State:
        base_data = getattr(state, "data", {})
        if not isinstance(base_data, dict):
            base_data = {}

        # Copia per non modificare in-place
        data: Dict[str, Any] = dict(base_data)

        value = data.get("value", 0)
        history = _get_history(data)

        # Nuovo value e nuova history
        new_value = value * factor
        new_history = history + [new_value]

        # Aggiorna campi dello stato
        data["value"] = new_value
        data["history"] = new_history
        data["channels"] = _update_channels_from_history(new_history, size=3)

        return State(data=data)

    return transition
