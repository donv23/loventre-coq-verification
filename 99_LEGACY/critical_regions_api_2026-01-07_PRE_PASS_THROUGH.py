"""
critical_regions_api.py

Mini API di alto livello per interrogare il seed discreto delle regioni
critiche del Loventre Engine.

Questa API NON ricalcola nulla: si limita a esporre in forma compatta
la classificazione che abbiamo fissato sperimentalmente nella tabella
del seed (param, factor) ∈ {1,2,3} × {1,2,3}.
"""


from typing import Dict, Tuple, Any


# Mappa compatta delle 9 combinazioni (param, factor)
# I dati sono quelli emersi da:
# - critical_signature_lab.py
# - critical_regions_seed.py
#
# Per ogni coppia memorizziamo:
# - region_type: "regular_region" / "precritical_region" / "critical_region"
# - pattern_label_short: etichetta Pattern C su history corta
# - multi_critical_long: True/False (regime multicanale critico su history lunga)
# - spread_short: channels_spread su history corta
# - spread_long: channels_spread su history lunga
CRITICAL_REGION_MAP: Dict[Tuple[int, int], Dict[str, Any]] = {
    (1, 1): {
        "region_type": "regular_region",
        "pattern_label_short": "regular_configuration",
        "multi_critical_long": False,
        "spread_short": 1,
        "spread_long": 1,
    },
    (1, 2): {
        "region_type": "regular_region",
        "pattern_label_short": "regular_configuration",
        "multi_critical_long": True,
        "spread_short": 2,
        "spread_long": 1024,
    },
    (1, 3): {
        "region_type": "precritical_region",
        "pattern_label_short": "mixed_configuration",
        "multi_critical_long": True,
        "spread_short": 3,
        "spread_long": 59049,
    },
    (2, 1): {
        "region_type": "regular_region",
        "pattern_label_short": "regular_configuration",
        "multi_critical_long": False,
        "spread_short": 2,
        "spread_long": 2,
    },
    (2, 2): {
        "region_type": "precritical_region",
        "pattern_label_short": "geometric_precritical_configuration",
        "multi_critical_long": True,
        "spread_short": 4,
        "spread_long": 2048,
    },
    (2, 3): {
        "region_type": "critical_region",
        "pattern_label_short": "fully_critical_configuration",
        "multi_critical_long": True,
        "spread_short": 6,
        "spread_long": 118098,
    },
    (3, 1): {
        "region_type": "precritical_region",
        "pattern_label_short": "geometric_precritical_configuration",
        "multi_critical_long": True,
        "spread_short": 3,
        "spread_long": 3,
    },
    (3, 2): {
        "region_type": "critical_region",
        "pattern_label_short": "fully_critical_configuration",
        "multi_critical_long": True,
        "spread_short": 6,
        "spread_long": 3072,
    },
    (3, 3): {
        "region_type": "critical_region",
        "pattern_label_short": "fully_critical_configuration",
        "multi_critical_long": True,
        "spread_short": 9,
        "spread_long": 177147,
    },
}


def classify_region(param: int, factor: int) -> str:
    """
    Restituisce il tipo di regione per la coppia (param, factor):

      - "regular_region"
      - "precritical_region"
      - "critical_region"

    Se la coppia non è nel seed discreto, solleva ValueError.
    """
    key = (param, factor)
    if key not in CRITICAL_REGION_MAP:
        raise ValueError(f"Coppia (param={param}, factor={factor}) fuori dal seed discreto.")
    return CRITICAL_REGION_MAP[key]["region_type"]  # type: ignore[return-value]


def is_seed_canonico(param: int, factor: int) -> bool:
    """
    Restituisce True se (param, factor) coincide con il seed critico canonico.

    Per costruzione, il seed critico canonico è (param, factor) = (2, 3),
    che ha:
      - Pattern C = fully_critical_configuration su history corta
      - regime 1D critico ad alta entropia
      - regime multicanale critico ad alta diffusione su history lunga
    """
    return (param, factor) == (2, 3)


def get_region_signature(param: int, factor: int) -> Dict[str, Any]:
    """
    Restituisce l'intera "firma" discreta associata alla coppia (param, factor).

    Il dizionario risultante contiene le chiavi:
      - "region_type"
      - "pattern_label_short"
      - "multi_critical_long"
      - "spread_short"
      - "spread_long"

    Se la coppia non è nel seed, solleva ValueError.
    """
    key = (param, factor)
    if key not in CRITICAL_REGION_MAP:
        raise ValueError(f"Coppia (param={param}, factor={factor}) fuori dal seed discreto.")
    return dict(CRITICAL_REGION_MAP[key])


def list_all_regions() -> Dict[Tuple[int, int], Dict[str, Any]]:
    """
    Restituisce una copia dell'intera mappa discreta delle regioni.

    Utile se, in futuro, vuoi scorrere tutte le combinazioni in un contesto
    esterno (es. per stampe, visualizzazioni, oppure per collegare il seed
    ad una tabella simbolica nella dimostrazione).
    """
    return {k: dict(v) for k, v in CRITICAL_REGION_MAP.items()}


# Piccola demo se eseguito come script
if __name__ == "__main__":
    print("=== Loventre Engine – Critical Regions API demo ===\n")

    for param in (1, 2, 3):
        for factor in (1, 2, 3):
            key = (param, factor)
            sig = CRITICAL_REGION_MAP[key]
            region = sig["region_type"]
            pattern = sig["pattern_label_short"]
            multi_crit = sig["multi_critical_long"]
            spread_s = sig["spread_short"]
            spread_l = sig["spread_long"]
            canonico = is_seed_canonico(param, factor)

            print(f"(param={param}, factor={factor})")
            print(
                f"  region_type       : {region}\n"
                f"  PatternC(short)   : {pattern}\n"
                f"  multi_critical    : {multi_crit}\n"
                f"  spread_short      : {spread_s}\n"
                f"  spread_long       : {spread_l}\n"
                f"  is_seed_canonico  : {canonico}"
            )
            print("--------------------------------------------------")

