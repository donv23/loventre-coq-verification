"""
loventre_toy_table.py

Modulo di classificazione toy per il Loventre Engine:
- regioni regolare / precritica / critica / mista,
- classi P_like / NP_like,
- regimi temporali short / long.

Tutto è codificato "a tabella" usando i risultati osservati in:
- pipeline_regimes_lab.py
- pipeline_multichannel_long_history.py
- critical_signature_lab.py
"""

from typing import Literal, Tuple, Dict

Param = int
Factor = int
Params = Tuple[Param, Factor]

RegionLabel = Literal["regular", "precritical", "critical", "mixed"]
TimeRegime = Literal["time_euclidean", "time_threshold", "time_hyperbolic", "time_mixed"]


# --- TABELLA PRINCIPALE: TUTTO IN UN SOLO POSTO ---------------------------------

# Per ogni (param, factor) inseriamo:
# - region : regular / precritical / critical / mixed
# - time_short : regime temporale sulla history corta
# - time_long  : regime temporale sulla history lunga
#
# I valori qui sotto sono copiati/astratti dagli output che hai già ottenuto
# da pipeline_regimes_lab.py e pipeline_multichannel_long_history.py.

TOY_GRID: Dict[Params, Dict[str, object]] = {
    # param = 1
    (1, 1): {
        "region": "regular",
        "time_short": "time_euclidean",
        "time_long": "time_euclidean",
    },
    (1, 2): {
        "region": "precritical",
        "time_short": "time_euclidean",
        "time_long": "time_threshold",
    },
    (1, 3): {
        "region": "mixed",
        "time_short": "time_mixed",
        "time_long": "time_mixed",
    },
    # param = 2
    (2, 1): {
        "region": "regular",
        "time_short": "time_euclidean",
        "time_long": "time_euclidean",
    },
    (2, 2): {
        "region": "precritical",
        "time_short": "time_threshold",
        "time_long": "time_threshold",
    },
    (2, 3): {
        "region": "critical",
        "time_short": "time_hyperbolic",
        "time_long": "time_hyperbolic",
    },
    # param = 3
    (3, 1): {
        "region": "precritical",
        "time_short": "time_threshold",
        "time_long": "time_threshold",
    },
    (3, 2): {
        "region": "critical",
        "time_short": "time_hyperbolic",
        "time_long": "time_hyperbolic",
    },
    (3, 3): {
        "region": "critical",
        "time_short": "time_hyperbolic",
        "time_long": "time_hyperbolic",
    },
}


# --- FUNZIONI DI ACCESSO ---------------------------------------------------------


def get_region(param: int, factor: int) -> RegionLabel:
    """
    Restituisce la regione: 'regular', 'precritical', 'critical' oppure 'mixed'.
    """
    key = (param, factor)
    info = TOY_GRID.get(key)
    if info is None:
        raise ValueError(f"Parametri fuori griglia toy: {key}")
    return info["region"]  # type: ignore[return-value]


def is_P_like(param: int, factor: int) -> bool:
    """
    Definizione P_like (versione toy):
      P_like = region regular U precritical
    """
    region = get_region(param, factor)
    return region in ("regular", "precritical")


def is_NP_like(param: int, factor: int) -> bool:
    """
    Definizione NP_like (versione toy):
      NP_like = region critical
    """
    region = get_region(param, factor)
    return region == "critical"


def get_time_short(param: int, factor: int) -> TimeRegime:
    """
    Regime temporale SHORT 'a tabella', coerente con i risultati di pipeline_regimes_lab.py.
    """
    key = (param, factor)
    info = TOY_GRID.get(key)
    if info is None:
        raise ValueError(f"Parametri fuori griglia toy: {key}")
    return info["time_short"]  # type: ignore[return-value]


def get_time_long(param: int, factor: int) -> TimeRegime:
    """
    Regime temporale LONG 'a tabella', coerente con i risultati di
    pipeline_multichannel_long_history.py.
    """
    key = (param, factor)
    info = TOY_GRID.get(key)
    if info is None:
        raise ValueError(f"Parametri fuori griglia toy: {key}")
    return info["time_long"]  # type: ignore[return-value]


# --- PICCOLO MAIN DI TEST --------------------------------------------------------


def main() -> None:
    print("=== Loventre Toy Table – Classificazione P_like / NP_like + tempo ===")
    for param in [1, 2, 3]:
        for factor in [1, 2, 3]:
            region = get_region(param, factor)
            p_like = is_P_like(param, factor)
            np_like = is_NP_like(param, factor)
            t_short = get_time_short(param, factor)
            t_long = get_time_long(param, factor)
            print("--------------------------------------------------")
            print(f"(param={param}, factor={factor})")
            print(f"  region      : {region}")
            print(f"  P_like      : {p_like}")
            print(f"  NP_like     : {np_like}")
            print(f"  time_short  : {t_short}")
            print(f"  time_long   : {t_long}")
    print("--------------------------------------------------")


if __name__ == "__main__":
    main()
