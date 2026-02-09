"""
critical_signature_lab.py

Piccolo script standalone che stampa una tabella sintetica
delle “firme” (regimi 1D, multicanale, Pattern C e regime temporale)
per i parametri (param, factor) che abbiamo già esplorato nei vari pipeline_*.py.

Non ricalcola le metriche di base: usa i valori già osservati sperimentalmente
(per regime_1d_*, regime_multi_*, Pattern C, spread, multi_critical_long)
e in più deriva in modo puramente simbolico un regime temporale short/long:

- time_euclidean   : tempo quasi lineare (regimi regolari)
- time_threshold   : zona di soglia / precritica / soglia di esplosione
- time_hyperbolic  : tempo iperbolico, tipico delle regioni pienamente critiche
- time_mixed       : casi misti / non classificati
"""

GRID_SIGNATURES = [
    {
        "param": 1,
        "factor": 1,
        "regime_1d_short": "stable_low_variation",
        "regime_multi_short": "mixed_intermediate",
        "pattern_c": "regular_configuration",
        "channels_spread_short": 1,
        "regime_1d_long": "intermediate",
        "regime_multi_long": "synchronized_low_spread",
        "channels_spread_long": 1,
        "multi_critical_long": False,
    },
    {
        "param": 1,
        "factor": 2,
        "regime_1d_short": "stable_low_variation",
        "regime_multi_short": "mixed_intermediate",
        "pattern_c": "regular_configuration",
        "channels_spread_short": 2,
        "regime_1d_long": "critical_high_entropy",
        "regime_multi_long": "synchronized_high_spread",
        "channels_spread_long": 1024,
        "multi_critical_long": True,
    },
    {
        "param": 1,
        "factor": 3,
        "regime_1d_short": "intermediate",
        "regime_multi_short": "mixed_intermediate",
        "pattern_c": "mixed_configuration",
        "channels_spread_short": 3,
        "regime_1d_long": "critical_high_entropy",
        "regime_multi_long": "synchronized_high_spread",
        "channels_spread_long": 59049,
        "multi_critical_long": True,
    },
    {
        "param": 2,
        "factor": 1,
        "regime_1d_short": "stable_low_variation",
        "regime_multi_short": "mixed_intermediate",
        "pattern_c": "regular_configuration",
        "channels_spread_short": 2,
        "regime_1d_long": "intermediate",
        "regime_multi_long": "synchronized_low_spread",
        "channels_spread_long": 2,
        "multi_critical_long": False,
    },
    {
        "param": 2,
        "factor": 2,
        "regime_1d_short": "intermediate",
        "regime_multi_short": "desynchronized_high_spread",
        "pattern_c": "geometric_precritical_configuration",
        "channels_spread_short": 4,
        "regime_1d_long": "critical_high_entropy",
        "regime_multi_long": "synchronized_high_spread",
        "channels_spread_long": 2048,
        "multi_critical_long": True,
    },
    {
        "param": 2,
        "factor": 3,
        "regime_1d_short": "critical_high_entropy",
        "regime_multi_short": "desynchronized_high_spread",
        "pattern_c": "fully_critical_configuration",
        "channels_spread_short": 6,
        "regime_1d_long": "critical_high_entropy",
        "regime_multi_long": "synchronized_high_spread",
        "channels_spread_long": 118098,
        "multi_critical_long": True,
    },
    {
        "param": 3,
        "factor": 1,
        "regime_1d_short": "intermediate",
        "regime_multi_short": "desynchronized_high_spread",
        "pattern_c": "geometric_precritical_configuration",
        "channels_spread_short": 3,
        "regime_1d_long": "intermediate",
        "regime_multi_long": "synchronized_high_spread",
        "channels_spread_long": 3,
        "multi_critical_long": True,
    },
    {
        "param": 3,
        "factor": 2,
        "regime_1d_short": "critical_high_entropy",
        "regime_multi_short": "desynchronized_high_spread",
        "pattern_c": "fully_critical_configuration",
        "channels_spread_short": 6,
        "regime_1d_long": "critical_high_entropy",
        "regime_multi_long": "synchronized_high_spread",
        "channels_spread_long": 3072,
        "multi_critical_long": True,
    },
    {
        "param": 3,
        "factor": 3,
        "regime_1d_short": "critical_high_entropy",
        "regime_multi_short": "desynchronized_high_spread",
        "pattern_c": "fully_critical_configuration",
        "channels_spread_short": 9,
        "regime_1d_long": "critical_high_entropy",
        "regime_multi_long": "synchronized_high_spread",
        "channels_spread_long": 177147,
        "multi_critical_long": True,
    },
]


def classify_time_regime_short(row: dict) -> str:
    """
    Regime temporale basato solo sulla configurazione corta (Pattern C).

    - regular_configuration              -> time_euclidean
    - geometric_precritical_configuration -> time_threshold
    - fully_critical_configuration       -> time_hyperbolic
    - altrimenti                         -> time_mixed
    """
    pattern = row["pattern_c"]
    if pattern == "regular_configuration":
        return "time_euclidean"
    if pattern == "geometric_precritical_configuration":
        return "time_threshold"
    if pattern == "fully_critical_configuration":
        return "time_hyperbolic"
    return "time_mixed"


def classify_time_regime_long(row: dict) -> str:
    """
    Regime temporale lungo, in funzione di:
    - Pattern C (seed locale)
    - multi_critical_long (esplosione multicanale a lunga scala)

    Logica:
    - se multi_critical_long è False          -> time_euclidean
    - se multi_critical_long è True e
        Pattern C è regular/precritical       -> time_threshold
    - se multi_critical_long è True e
        Pattern C è fully_critical            -> time_hyperbolic
    - altrimenti                              -> time_mixed
    """
    pattern = row["pattern_c"]
    multi_crit = row["multi_critical_long"]

    if not multi_crit:
        return "time_euclidean"

    if pattern in (
        "regular_configuration",
        "geometric_precritical_configuration",
    ):
        return "time_threshold"

    if pattern == "fully_critical_configuration":
        return "time_hyperbolic"

    return "time_mixed"


def main() -> None:
    print("=== Loventre Engine – Tabella sintetica delle firme (seed) ===")
    print()
    for row in GRID_SIGNATURES:
        time_short = classify_time_regime_short(row)
        time_long = classify_time_regime_long(row)

        print("--------------------------------------------------")
        print(f"param = {row['param']}, factor = {row['factor']}")
        print(
            "  [SHORT] "
            f"1D={row['regime_1d_short']}, "
            f"multi={row['regime_multi_short']}, "
            f"PatternC={row['pattern_c']}, "
            f"spread={row['channels_spread_short']}, "
            f"time={time_short}"
        )
        print(
            "  [LONG ] "
            f"1D={row['regime_1d_long']}, "
            f"multi={row['regime_multi_long']}, "
            f"spread={row['channels_spread_long']}, "
            f"multi_critical={row['multi_critical_long']}, "
            f"time={time_long}"
        )
    print("--------------------------------------------------")
    print(
        "Nota: (param=2, factor=3) è il seed critico di riferimento "
        "(PatternC=fully_critical_configuration su history corta)."
    )


if __name__ == "__main__":
    main()
