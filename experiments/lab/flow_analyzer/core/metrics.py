def _get_value_from_state(state):
    """
    Estrae in modo sicuro state.data["value"].
    Se manca, restituisce 0.
    """
    data = getattr(state, "data", {})
    if isinstance(data, dict):
        return data.get("value", 0)
    return 0


def _get_history_from_state(state):
    """
    Estrae in modo sicuro state.data["history"] come lista.
    Se manca o non è lista/tupla, restituisce None.
    """
    data = getattr(state, "data", {})
    if not isinstance(data, dict):
        return None

    history = data.get("history", None)
    if isinstance(history, (list, tuple)):
        return list(history)
    return None


def compute_curvature(state):
    """
    Curvatura informazionale molto semplice:
    value^2 come proxy di intensità.
    """
    value = _get_value_from_state(state)
    return float(value * value)


def compute_entropy(state):
    """
    Entropia basata sulla history:
    media delle differenze assolute tra valori consecutivi.
    Se la history non è disponibile o troppo corta,
    usa |value| come fallback.
    """
    history = _get_history_from_state(state)

    # Fallback se non abbiamo history utile
    if not history or len(history) < 2:
        value = _get_value_from_state(state)
        return float(abs(value))

    diffs = []
    for i in range(len(history) - 1):
        a = history[i]
        b = history[i + 1]
        if isinstance(a, (int, float)) and isinstance(b, (int, float)):
            diffs.append(abs(b - a))

    if not diffs:
        value = _get_value_from_state(state)
        return float(abs(value))

    return float(sum(diffs) / len(diffs))


def compute_criticality(state):
    """
    Criticalità binaria:
    1.0 se |value| > 1, altrimenti 0.0.
    """
    value = _get_value_from_state(state)
    return 1.0 if abs(value) > 1 else 0.0


def compute_all_metrics(state):
    """
    Restituisce le metriche derivate dallo stato.
    """
    return {
        "curvature": compute_curvature(state),
        "entropy": compute_entropy(state),
        "criticality": compute_criticality(state),
    }
