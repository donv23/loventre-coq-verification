def analyze_trajectory(state, metrics):
    """
    Analizza la traiettoria del flusso usando:
    - history nello state
    - curvature / entropy / criticality nelle metriche

    Restituisce un dizionario con un profilo qualitativo del flusso.
    """
    # Estrazione sicura di history
    data = getattr(state, "data", {})
    history = None
    length = 0

    if isinstance(data, dict):
        h = data.get("history")
        if isinstance(h, (list, tuple)):
            history = list(h)
            length = len(history)

    # Estrazione sicura delle metriche
    curvature = float(metrics.get("curvature", 0.0))
    entropy = float(metrics.get("entropy", 0.0))
    criticality = float(metrics.get("criticality", 0.0))

    # Regole molto semplici per classificare il regime del flusso
    if criticality >= 1.0 and entropy > 2.0 and curvature > 10.0:
        regime = "critical_high_entropy"
    elif curvature < 1.0 and entropy < 1.0 and criticality < 1.0:
        regime = "stable_low_variation"
    else:
        regime = "intermediate"

    profile = {
        "regime": regime,
        "length": length,
        # Usiamo entropy come proxy di ampiezza media del passo
        "avg_step": entropy,
        "curvature": curvature,
        "entropy": entropy,
        "criticality": criticality,
    }

    # Aggiungiamo una piccola coda della history per debug
    if history is not None:
        if length <= 3:
            profile["history_tail"] = history
        else:
            profile["history_tail"] = history[-3:]

    # Nota descrittiva
    if regime == "critical_high_entropy":
        profile["notes"] = "Flusso accelerato e critico su scala breve."
    elif regime == "stable_low_variation":
        profile["notes"] = "Flusso stabile, variazioni piccole e non critico."
    else:
        profile["notes"] = "Flusso in regime intermedio."

    return profile
