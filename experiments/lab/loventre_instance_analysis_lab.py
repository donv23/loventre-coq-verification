from loventre_instance_analysis import analyze_instance, suggest_strategy
from loventre_instance_analysis import detect_complexity_horizon


def build_history_regular():
    """
    History 'regolare': C e H bassi, nessun passo davvero in barriera.
    """
    history = []
    for t in range(12):
        C_t = 0.1 * t          # complessita' lenta
        H_t = 0.05 * (t % 4)   # entropia bassa
        history.append({"C": C_t, "H": H_t})
    return history


def build_history_precritical():
    """
    History 'precritical': la maggior parte dei passi e' sotto soglia,
    ma ci sono alcuni picchi che formano segmenti di barriera corti.
    """
    history = []
    base_C = [0.2, 0.3, 0.5, 0.8, 1.2, 0.6, 0.4, 1.0, 1.3, 0.7, 0.5, 0.9]
    base_H = [0.1, 0.2, 0.4, 0.7, 1.0, 0.5, 0.3, 0.8, 1.1, 0.6, 0.4, 0.9]
    for C_t, H_t in zip(base_C, base_H):
        history.append({"C": C_t, "H": H_t})
    return history


def build_history_critical():
    """
    History 'critical': una zona centrale con C e H alti per molti step
    consecutivi, che crea una barriera spessa.
    """
    history = []

    # zona iniziale bassa
    for t in range(4):
        C_t = 0.2 * t
        H_t = 0.1 * (t % 3)
        history.append({"C": C_t, "H": H_t})

    # zona critica (curvatura + entropia alte per piu' passi)
    critical_C = [1.5, 1.8, 2.0, 2.1, 2.2, 2.3]
    critical_H = [1.0, 1.1, 1.2, 1.2, 1.3, 1.3]
    for C_t, H_t in zip(critical_C, critical_H):
        history.append({"C": C_t, "H": H_t})

    # coda di rilassamento
    for t in range(4):
        C_t = 1.0 - 0.1 * t
        H_t = 0.8 - 0.1 * t
        history.append({"C": C_t, "H": H_t})

    return history


def run_scenario(name, history, E=1.0, V0_quantile=0.9):
    """
    Esegue analyze_instance + suggest_strategy su una history,
    e stampa un mini-rapporto Loventre.
    """
    print()
    print("==================================================")
    print(f"=== SCENARIO: {name}                         ===")
    print("==================================================")

    metrics = analyze_instance(
        history,
        alpha=1.0,
        beta=1.0,
        G_L=1.0,
        lambda_L=0.0,
        V0=None,
        V0_quantile=V0_quantile,
        E=E,
    )

    suggestion = suggest_strategy(metrics)
    horizon_info = detect_complexity_horizon(
        metrics,
        window_size=10,
        horizon_U_factor=0.9,
        horizon_barrier_occupancy=0.3,
        horizon_p_tunnel_max=1e-6,
        black_hole_p_tunnel_max=1e-10,
    )

    print(f"V0 stimato:           {metrics['V0']:.4f}")
    print(f"a_min (spessore):     {metrics['a_min']:.2f}")
    print(f"Energia E:            {metrics['E']:.3f}")
    print(f"p_tunnel:             {metrics['p_tunnel']:.3e}")
    print(f"Tentativi medi attesi:{metrics['expected_attempts']:.3e}")
    print(f"Classificazione:      {metrics['classification']}")
    print(f"Occupazione barriera: {metrics['barrier_occupancy']:.3f}")
    print(f"Orizzonte rilevato:   {horizon_info['horizon_detected']}")
    print(f"Rischio buco nero:    {horizon_info['black_hole_risk']}")
    print(f"Suggerimento:         {suggestion}")


def main():
    # Parametri di prova (puoi giocarci dopo)
    E = 1.0
    V0_quantile = 0.9

    # Costruisci i tre scenari toy
    hist_reg = build_history_regular()
    hist_pre = build_history_precritical()
    hist_crit = build_history_critical()

    # Esegui analisi per ognuno
    run_scenario("REGOLARE", hist_reg, E=E, V0_quantile=V0_quantile)
    run_scenario("PRECRITICAL", hist_pre, E=E, V0_quantile=V0_quantile)
    run_scenario("CRITICAL", hist_crit, E=E, V0_quantile=V0_quantile)


if __name__ == "__main__":
    main()