"""
loventre_seed_report.py

Dossier completo per un singolo seed (param, factor) del Loventre Engine.

Modalità d'uso (da terminale):

  - Seed critico di riferimento (2,3):
      python3 loventre_seed_report.py

  - Seed generico (es. 1,1):
      python3 loventre_seed_report.py 1 1

Per ogni seed selezionato combina:
- output della pipeline short (pipeline_regimes_lab.run_experiment),
- output della pipeline long (pipeline_multichannel_long_history.run_iterated_experiment),
- firma sintetica da critical_signature_lab.GRID_SIGNATURES,
- classificazione P_like / NP_like e regimi temporali da loventre_toy_table,
- un Loventre Score toy (quanto è critico / NP-like il seed),
- una stima toy della probabilità di "tunneling creativo" oltre la barriera
  di complessità associata a quel seed.
"""

import sys
from math import log10
from typing import Any, Dict, Optional, Tuple

from loventre_tunneling import (
    compute_potential,
    p_tunnel,
    expected_attempts,
)

from pipeline_regimes_lab import run_experiment
from pipeline_multichannel_long_history import run_iterated_experiment
from critical_signature_lab import GRID_SIGNATURES
from loventre_toy_table import (
    get_region,
    is_P_like,
    is_NP_like,
    get_time_short,
    get_time_long,
)

# ---------------------------------------------------------------------
# CONFIGURAZIONE DI DEFAULT DEL SEED
# ---------------------------------------------------------------------

DEFAULT_SEED_PARAM: int = 2
DEFAULT_SEED_FACTOR: int = 3
ITERATIONS_LONG: int = 10
SPREAD_THRESHOLD: float = 2.0

# ---------------------------------------------------------------------
# CONFIGURAZIONE TOY PER IL TUNNELING
# (da calibrare in futuro in base ai dati reali del motore)
# ---------------------------------------------------------------------

ALPHA_POTENTIAL: float = 1.0   # peso "curvatura effettiva"
BETA_POTENTIAL: float = 1.0    # peso "entropia effettiva"
A_MIN_BARRIER: float = 4.0     # spessore minimo della barriera (in step/stati "duri")
ENERGY_LEVEL: float = 0.5      # energia/risorse assegnate alla run


# ---------------------------------------------------------------------
# LOVENTRE SCORE (versione interna al seed report)
# ---------------------------------------------------------------------

PATTERN_SCORE: Dict[str, float] = {
    "regular_configuration": 0.0,
    "mixed_configuration": 0.3,
    "geometric_precritical_configuration": 0.6,
    "fully_critical_configuration": 1.0,
}

TIME_SCORE: Dict[str, float] = {
    "time_euclidean": 0.0,
    "time_mixed": 0.3,
    "time_threshold": 0.6,
    "time_hyperbolic": 1.0,
}


def normalize_spread(spread_long: float) -> float:
    """
    Normalizza lo spread lungo in [0,1] circa usando un log10.

    Per i nostri valori tipici:
      - spread_long = 1        -> ~0.06
      - spread_long = 1024     -> ~0.6
      - spread_long = 59049    -> ~0.9
      - spread_long = 177147   -> ~1.0 (clippato)
    """
    if spread_long <= 0:
        return 0.0
    return min(1.0, log10(1.0 + spread_long) / 5.0)


def find_signature_entry(param: int, factor: int) -> Optional[Dict[str, Any]]:
    """
    Cerca nella GRID_SIGNATURES la riga corrispondente a (param, factor).
    """
    for row in GRID_SIGNATURES:
        if row.get("param") == param and row.get("factor") == factor:
            return row
    return None


def compute_loventre_score_from_entry(entry: Dict[str, Any]) -> float:
    """
    Calcola un Loventre Score toy partendo da una entry della GRID_SIGNATURES.
    """
    param = entry["param"]
    factor = entry["factor"]
    pattern_c = entry["pattern_c"]
    spread_long = float(entry["channels_spread_long"])
    multi_crit = bool(entry["multi_critical_long"])

    pattern_score = PATTERN_SCORE.get(pattern_c, 0.0)
    spread_score = normalize_spread(spread_long)

    time_long = get_time_long(param, factor)
    time_score = TIME_SCORE.get(time_long, 0.0)

    multi_score = 1.0 if multi_crit else 0.0

    score = (
        0.4 * pattern_score
        + 0.3 * spread_score
        + 0.2 * time_score
        + 0.1 * multi_score
    )
    return score


def compute_tunneling_from_entry(entry: Dict[str, Any]) -> Dict[str, float]:
    """
    Stima toy del "tunneling creativo" oltre la barriera di complessità
    associata a questo seed, usando solo informazioni aggregate della
    GRID_SIGNATURES.

    Idea:
      - Curvatura effettiva κ_eff ≈ PATTERN_SCORE(pattern_c)
      - Entropia effettiva H_eff ≈ normalize_spread(channels_spread_long)
      - Potenziale di barriera V0 ≈ U_eff = α * κ_eff + β * H_eff
      - p_tunnel = exp(-2 * sqrt(V0 - E) * a_min) se E < V0

    Questo NON usa direttamente le kappa/H istantanee del motore, ma
    una compressione toy basata su:
      - criticità del pattern C,
      - ampiezza dello spread lungo.
    """
    param = entry["param"]
    factor = entry["factor"]

    pattern_c = entry["pattern_c"]
    spread_long = float(entry["channels_spread_long"])

    pattern_score = PATTERN_SCORE.get(pattern_c, 0.0)
    spread_norm = normalize_spread(spread_long)

    # Curvatura ed entropia "effettive" in [0,1] circa
    kappa_eff = pattern_score
    entropy_eff = spread_norm

    # Potenziale di barriera toy per questo seed
    V0 = compute_potential(
        kappa_eff,
        entropy_eff,
        alpha=ALPHA_POTENTIAL,
        beta=BETA_POTENTIAL,
    )

    p = p_tunnel(V0, A_MIN_BARRIER, ENERGY_LEVEL)
    N_mean = expected_attempts(p)

    return {
        "V0": V0,
        "kappa_eff": kappa_eff,
        "entropy_eff": entropy_eff,
        "p_tunnel": p,
        "expected_attempts": N_mean,
    }


def parse_seed_from_argv() -> Tuple[int, int]:
    """
    Legge (param, factor) da riga di comando, se presenti.
    Se non ci sono argomenti, usa il seed critico di default (2,3).

    Esempi:
      python3 loventre_seed_report.py        -> (2,3)
      python3 loventre_seed_report.py 1 1    -> (1,1)
      python3 loventre_seed_report.py 3 2    -> (3,2)
    """
    if len(sys.argv) >= 3:
        try:
            param = int(sys.argv[1])
            factor = int(sys.argv[2])
            return param, factor
        except ValueError:
            print("[ATTENZIONE] Argomenti non numerici, uso il seed di default (2,3).")
            return DEFAULT_SEED_PARAM, DEFAULT_SEED_FACTOR
    else:
        return DEFAULT_SEED_PARAM, DEFAULT_SEED_FACTOR


# ---------------------------------------------------------------------
# MAIN: DOSSIER COMPLETO DEL SEED
# ---------------------------------------------------------------------


def main() -> None:
    param, factor = parse_seed_from_argv()
    seed: Tuple[int, int] = (param, factor)

    print("==================================================================")
    print("=== Loventre Seed Report – Dossier completo per un singolo seed ===")
    print("==================================================================")
    print(f"Seed scelto: (param={param}, factor={factor})")
    print()

    # -----------------------------------------------------------------
    # BLOCCO A – History corta: pipeline_regimes_lab
    # -----------------------------------------------------------------
    print(">>> BLOCCO A – History corta (pipeline_regimes_lab.run_experiment)")
    run_experiment(param, factor)
    print()

    # -----------------------------------------------------------------
    # BLOCCO B – History lunga: pipeline_multichannel_long_history
    # -----------------------------------------------------------------
    print(">>> BLOCCO B – History lunga (pipeline_multichannel_long_history.run_iterated_experiment)")
    _summary_long = run_iterated_experiment(
        param=param,
        factor=factor,
        iterations=ITERATIONS_LONG,
        spread_threshold=SPREAD_THRESHOLD,
        verbose=True,
    )
    print()

    # -----------------------------------------------------------------
    # BLOCCO C – Firma sintetica + classificazione + Loventre Score
    # -----------------------------------------------------------------
    print(">>> BLOCCO C – Firma sintetica + P_like / NP_like + Loventre Score")
    entry = find_signature_entry(param, factor)
    if entry is None:
        print(f"[ATTENZIONE] Nessuna entry trovata in GRID_SIGNATURES per il seed {seed}.")
        print("            (Sei fuori dalla griglia toy {1,2,3} x {1,2,3}.)")
        return

    region = get_region(param, factor)
    p_like = is_P_like(param, factor)
    np_like = is_NP_like(param, factor)
    time_short = get_time_short(param, factor)
    time_long = get_time_long(param, factor)

    pattern_c = entry["pattern_c"]
    spread_short = entry["channels_spread_short"]
    spread_long = entry["channels_spread_long"]
    multi_crit = entry["multi_critical_long"]

    loventre_score = compute_loventre_score_from_entry(entry)

    print("--------------------------------------------------")
    print(f"(param={param}, factor={factor}) – Firma Loventre Toy")
    print(f"  region                 : {region}")
    print(f"  P_like / NP_like       : P_like={p_like}, NP_like={np_like}")
    print(f"  Pattern C              : {pattern_c}")
    print(f"  channels_spread_short  : {spread_short}")
    print(f"  channels_spread_long   : {spread_long}")
    print(f"  multi_critical_long    : {multi_crit}")
    print(f"  time_short (toy table) : {time_short}")
    print(f"  time_long  (toy table) : {time_long}")
    print(f"  Loventre Score (toy)   : {loventre_score:.3f}")
    print("--------------------------------------------------")
    print("Nota: score vicino a 0 → seed regolare; score vicino a 1 → seed critico / NP-like.")
    print()

    # -----------------------------------------------------------------
    # BLOCCO D – Tunneling creativo oltre la barriera di complessità
    # -----------------------------------------------------------------
    print(">>> BLOCCO D – Tunneling creativo oltre la barriera di complessità (toy)")

    tunneling_info = compute_tunneling_from_entry(entry)

    V0 = tunneling_info["V0"]
    kappa_eff = tunneling_info["kappa_eff"]
    entropy_eff = tunneling_info["entropy_eff"]
    p = tunneling_info["p_tunnel"]
    N_mean = tunneling_info["expected_attempts"]

    print("Stima toy del potenziale e della probabilità di salto:")
    print(f"  kappa_eff (curvatura eff.)   : {kappa_eff:.3f}")
    print(f"  entropy_eff (entropia eff.)  : {entropy_eff:.3f}")
    print(f"  V0 (potenziale barriera)     : {V0:.4f}")
    print(f"  a_min (spessore barriera)    : {A_MIN_BARRIER}")
    print(f"  Energia E                    : {ENERGY_LEVEL}")
    print(f"  p_tunnel (per tentativo)     : {p:.3e}")
    print(f"  Tentativi medi attesi E[N]   : {N_mean:.3e}")
    print()
    print("Interpretazione (toy):")
    print("  - kappa_eff alto + entropy_eff alta → barriera più dura (V0 più grande).")
    print("  - p_tunnel molto piccolo → serve un numero enorme di tentativi medi per un")
    print("    'lampo di invenzione' che attraversa la barriera rispetto alle risorse E.")
    print()

    print("=== Fine Loventre Seed Report ===")


if __name__ == "__main__":
    main()
