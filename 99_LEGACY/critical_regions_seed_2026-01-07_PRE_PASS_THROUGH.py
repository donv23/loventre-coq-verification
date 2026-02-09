"""
Modulo seed per le *regioni critiche* nel piano (param, factor).

Questo file non esegue calcoli: codifica in forma compatta
ciò che abbiamo osservato sperimentalmente con:

- pipeline_regimes_lab.py              (history corta)
- pipeline_multichannel_long_history.py (history lunga)
- pattern_classifier.py
- critical_signature_lab.py

Per ogni coppia (param, factor) con param,factor in {1,2,3}
assegniamo un'etichetta qualitativa:

- "regular_region"     : configurazione regolare
                         (Pattern C = regular_configuration).
- "precritical_region" : configurazione precritica / mista
                         (Pattern C = geometric_precritical_configuration
                          oppure mixed_configuration).
- "critical_region"    : configurazione pienamente critica
                         (Pattern C = fully_critical_configuration).

La coppia (param=2, factor=3) è il *seed critico canonico*.
"""

from __future__ import annotations
from typing import Dict, Tuple, Any

RegionKey = Tuple[int, int]
RegionEntry = Dict[str, Any]

# ---------------------------------------------------------------------
# Dizionario principale con tutte le informazioni sul seed
# ---------------------------------------------------------------------

CRITICAL_REGION_SEED: Dict[RegionKey, RegionEntry] = {
    # --------------------------------------------------
    # param = 1
    # --------------------------------------------------
    (1, 1): {
        "region_type": "regular_region",
        "short": {
            "regime_1d": "stable_low_variation",
            "regime_multichannel": "mixed_intermediate",
            "pattern_c": "regular_configuration",
            "channels_spread": 1,
        },
        "long": {
            "regime_1d": "intermediate",
            "regime_multichannel": "synchronized_low_spread",
            "multi_critical": False,
            "channels_spread": 1,
        },
    },
    (1, 2): {
        "region_type": "regular_region",
        "short": {
            "regime_1d": "stable_low_variation",
            "regime_multichannel": "mixed_intermediate",
            "pattern_c": "regular_configuration",
            "channels_spread": 2,
        },
        "long": {
            "regime_1d": "critical_high_entropy",
            "regime_multichannel": "synchronized_high_spread",
            "multi_critical": True,
            "channels_spread": 1024,
        },
    },
    (1, 3): {
        "region_type": "precritical_region",
        "short": {
            "regime_1d": "intermediate",
            "regime_multichannel": "mixed_intermediate",
            "pattern_c": "mixed_configuration",
            "channels_spread": 3,
        },
        "long": {
            "regime_1d": "critical_high_entropy",
            "regime_multichannel": "synchronized_high_spread",
            "multi_critical": True,
            "channels_spread": 59049,
        },
    },

    # --------------------------------------------------
    # param = 2
    # --------------------------------------------------
    (2, 1): {
        "region_type": "regular_region",
        "short": {
            "regime_1d": "stable_low_variation",
            "regime_multichannel": "mixed_intermediate",
            "pattern_c": "regular_configuration",
            "channels_spread": 2,
        },
        "long": {
            "regime_1d": "intermediate",
            "regime_multichannel": "synchronized_low_spread",
            "multi_critical": False,
            "channels_spread": 2,
        },
    },
    (2, 2): {
        "region_type": "precritical_region",
        "short": {
            "regime_1d": "intermediate",
            "regime_multichannel": "desynchronized_high_spread",
            "pattern_c": "geometric_precritical_configuration",
            "channels_spread": 4,
        },
        "long": {
            "regime_1d": "critical_high_entropy",
            "regime_multichannel": "synchronized_high_spread",
            "multi_critical": True,
            "channels_spread": 2048,
        },
    },
    (2, 3): {
        "region_type": "critical_region",
        "short": {
            "regime_1d": "critical_high_entropy",
            "regime_multichannel": "desynchronized_high_spread",
            "pattern_c": "fully_critical_configuration",
            "channels_spread": 6,
        },
        "long": {
            "regime_1d": "critical_high_entropy",
            "regime_multichannel": "synchronized_high_spread",
            "multi_critical": True,
            "channels_spread": 118098,
        },
    },

    # --------------------------------------------------
    # param = 3
    # --------------------------------------------------
    (3, 1): {
        "region_type": "precritical_region",
        "short": {
            "regime_1d": "intermediate",
            "regime_multichannel": "desynchronized_high_spread",
            "pattern_c": "geometric_precritical_configuration",
            "channels_spread": 3,
        },
        "long": {
            "regime_1d": "intermediate",
            "regime_multichannel": "synchronized_high_spread",
            "multi_critical": True,
            "channels_spread": 3,
        },
    },
    (3, 2): {
        "region_type": "critical_region",
        "short": {
            "regime_1d": "critical_high_entropy",
            "regime_multichannel": "desynchronized_high_spread",
            "pattern_c": "fully_critical_configuration",
            "channels_spread": 6,
        },
        "long": {
            "regime_1d": "critical_high_entropy",
            "regime_multichannel": "synchronized_high_spread",
            "multi_critical": True,
            "channels_spread": 3072,
        },
    },
    (3, 3): {
        "region_type": "critical_region",
        "short": {
            "regime_1d": "critical_high_entropy",
            "regime_multichannel": "desynchronized_high_spread",
            "pattern_c": "fully_critical_configuration",
            "channels_spread": 9,
        },
        "long": {
            "regime_1d": "critical_high_entropy",
            "regime_multichannel": "synchronized_high_spread",
            "multi_critical": True,
            "channels_spread": 177147,
        },
    },
}

# Seed critico canonico (Pattern C pienamente critico su history corta)
CRITICAL_SEED_CANONICAL = {"param": 2, "factor": 3}


# ---------------------------------------------------------------------
# Funzioni di utilità
# ---------------------------------------------------------------------


def get_region_entry(param: int, factor: int) -> RegionEntry:
    """
    Restituisce l'entry completa del dizionario per (param, factor).

    Solleva ValueError se la coppia non è nel seed.
    """
    key = (param, factor)
    try:
        return CRITICAL_REGION_SEED[key]
    except KeyError as exc:
        raise ValueError(f"Coppia (param, factor) non presente nel seed: {key}") from exc


def get_region_type(param: int, factor: int) -> str:
    """
    Restituisce la label di regione:

    - "regular_region"
    - "precritical_region"
    - "critical_region"
    """
    entry = get_region_entry(param, factor)
    return entry["region_type"]


def is_regular_region(param: int, factor: int) -> bool:
    """True se (param, factor) è in regione regolare."""
    return get_region_type(param, factor) == "regular_region"


def is_precritical_region(param: int, factor: int) -> bool:
    """True se (param, factor) è in regione precritica."""
    return get_region_type(param, factor) == "precritical_region"


def is_critical_region(param: int, factor: int) -> bool:
    """True se (param, factor) è in regione pienamente critica."""
    return get_region_type(param, factor) == "critical_region"


def describe_region(param: int, factor: int) -> dict:
    """
    Restituisce un piccolo dizionario leggibile con:

    - param, factor
    - region_type
    - short / long (regimi, Pattern C, spread, multi_critical)
    """
    entry = get_region_entry(param, factor)
    return {
        "param": param,
        "factor": factor,
        "region_type": entry["region_type"],
        "short": entry["short"],
        "long": entry["long"],
    }


if __name__ == "__main__":
    # Piccolo self-test: stampa tutte le regioni in forma compatta
    print("=== Loventre Engine – Critical Region Seed ===")
    for param in (1, 2, 3):
        for factor in (1, 2, 3):
            entry = describe_region(param, factor)
            print(
                f"(param={param}, factor={factor}) -> "
                f"{entry['region_type']} | "
                f"PatternC(short)={entry['short']['pattern_c']} | "
                f"multi_critical(long)={entry['long']['multi_critical']}"
            )

