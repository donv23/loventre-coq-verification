from pprint import pprint

from multichannel_patterns import analyze_multichannel_history


def run_scenario(name, history, spread_threshold=2.0):
    print("==================================================")
    print(f"Scenario: {name}")
    print(f"history: {history}")

    profile = analyze_multichannel_history(
        history=history,
        window_size=3,
        stride=1,
        spread_threshold=spread_threshold,
    )

    print("Multichannel profile:")
    pprint(profile)
    print()


def main():
    # Scenario 1: crescita lenta e regolare -> synchronized_low_spread atteso
    history_slow = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

    # Scenario 2: crescita runaway monotona -> synchronized_high_spread atteso
    history_runaway = [0, 2, 4, 8, 16, 32, 64, 128]

    # Scenario 3: oscillazione forte con inversioni -> desynchronized_high_spread atteso
    # Pattern alternato positivo/negativo per forzare step desincronizzati
    history_oscillatory = [0, 5, -5, 5, -5, 5, -5, 5, -5]

    run_scenario("slow_monotone", history_slow, spread_threshold=2.0)
    run_scenario("runaway_monotone", history_runaway, spread_threshold=2.0)
    run_scenario("oscillatory_desync", history_oscillatory, spread_threshold=2.0)


if __name__ == "__main__":
    main()
