"""
Loventre Engine – Theory Bridge Seed

Questo modulo fornisce una rappresentazione compatta e puramente
funzionale delle firme seed per (param, factor) ∈ {1,2,3}×{1,2,3}.
È pensato come 'ponte' verso la formalizzazione in Coq.
"""

from dataclasses import dataclass
from typing import Dict, Tuple


@dataclass(frozen=True)
class SeedTheorySignature:
    param: int
    factor: int
    region_type: str
    pattern_short: str
    regime_1d_short: str
    regime_1d_long: str
    regime_multi_short: str
    regime_multi_long: str
    spread_short: int
    spread_long: int
    multi_critical_long: bool
    is_canonical_seed: bool


# Dizionario seed: TUTTO quello che serve alla teoria in forma discreta.
# I valori sono estratti da:
# - critical_signature_lab.py
# - critical_regions_seed.py
# - critical_regions_api.py
_SEED_THEORY_SIGNATURES: Dict[Tuple[int, int], SeedTheorySignature] = {
    (1, 1): SeedTheorySignature(
        param=1,
        factor=1,
        region_type="regular_region",
        pattern_short="regular_configuration",
        regime_1d_short="stable_low_variation",
        regime_1d_long="intermediate",
        regime_multi_short="mixed_intermediate",
        regime_multi_long="synchronized_low_spread",
        spread_short=1,
        spread_long=1,
        multi_critical_long=False,
        is_canonical_seed=False,
    ),
    (1, 2): SeedTheorySignature(
        param=1,
        factor=2,
        region_type="regular_region",
        pattern_short="regular_configuration",
        regime_1d_short="stable_low_variation",
        regime_1d_long="critical_high_entropy",
        regime_multi_short="mixed_intermediate",
        regime_multi_long="synchronized_high_spread",
        spread_short=2,
        spread_long=1024,
        multi_critical_long=True,
        is_canonical_seed=False,
    ),
    (1, 3): SeedTheorySignature(
        param=1,
        factor=3,
        region_type="precritical_region",
        pattern_short="mixed_configuration",
        regime_1d_short="intermediate",
        regime_1d_long="critical_high_entropy",
        regime_multi_short="mixed_intermediate",
        regime_multi_long="synchronized_high_spread",
        spread_short=3,
        spread_long=59049,
        multi_critical_long=True,
        is_canonical_seed=False,
    ),
    (2, 1): SeedTheorySignature(
        param=2,
        factor=1,
        region_type="regular_region",
        pattern_short="regular_configuration",
        regime_1d_short="stable_low_variation",
        regime_1d_long="intermediate",
        regime_multi_short="mixed_intermediate",
        regime_multi_long="synchronized_low_spread",
        spread_short=2,
        spread_long=2,
        multi_critical_long=False,
        is_canonical_seed=False,
    ),
    (2, 2): SeedTheorySignature(
        param=2,
        factor=2,
        region_type="precritical_region",
        pattern_short="geometric_precritical_configuration",
        regime_1d_short="intermediate",
        regime_1d_long="critical_high_entropy",
        regime_multi_short="desynchronized_high_spread",
        regime_multi_long="synchronized_high_spread",
        spread_short=4,
        spread_long=2048,
        multi_critical_long=True,
        is_canonical_seed=False,
    ),
    (2, 3): SeedTheorySignature(
        param=2,
        factor=3,
        region_type="critical_region",
        pattern_short="fully_critical_configuration",
        regime_1d_short="critical_high_entropy",
        regime_1d_long="critical_high_entropy",
        regime_multi_short="desynchronized_high_spread",
        regime_multi_long="synchronized_high_spread",
        spread_short=6,
        spread_long=118098,
        multi_critical_long=True,
        is_canonical_seed=True,  # seed canonico critico
    ),
    (3, 1): SeedTheorySignature(
        param=3,
        factor=1,
        region_type="precritical_region",
        pattern_short="geometric_precritical_configuration",
        regime_1d_short="intermediate",
        regime_1d_long="intermediate",
        regime_multi_short="desynchronized_high_spread",
        regime_multi_long="synchronized_high_spread",
        spread_short=3,
        spread_long=3,
        multi_critical_long=True,
        is_canonical_seed=False,
    ),
    (3, 2): SeedTheorySignature(
        param=3,
        factor=2,
        region_type="critical_region",
        pattern_short="fully_critical_configuration",
        regime_1d_short="critical_high_entropy",
        regime_1d_long="critical_high_entropy",
        regime_multi_short="desynchronized_high_spread",
        regime_multi_long="synchronized_high_spread",
        spread_short=6,
        spread_long=3072,
        multi_critical_long=True,
        is_canonical_seed=False,
    ),
    (3, 3): SeedTheorySignature(
        param=3,
        factor=3,
        region_type="critical_region",
        pattern_short="fully_critical_configuration",
        regime_1d_short="critical_high_entropy",
        regime_1d_long="critical_high_entropy",
        regime_multi_short="desynchronized_high_spread",
        regime_multi_long="synchronized_high_spread",
        spread_short=9,
        spread_long=177147,
        multi_critical_long=True,
        is_canonical_seed=False,
    ),
}


def get_seed_signature(param: int, factor: int) -> SeedTheorySignature:
    """
    Restituisce la firma teorica seed per (param, factor).

    È una funzione puramente deterministica, senza side-effect,
    adatta a essere tradotta in un lemma Coq del tipo:

      SeedSignature (param, factor) = ...

    """
    key = (param, factor)
    if key not in _SEED_THEORY_SIGNATURES:
        raise ValueError(
            f"Nessuna firma definita per (param={param}, factor={factor}). "
            "Il seed è definito solo per param,factor ∈ {1,2,3}."
        )
    return _SEED_THEORY_SIGNATURES[key]


def get_region_type(param: int, factor: int) -> str:
    """
    Restituisce solo il tipo di regione:
    'regular_region', 'precritical_region' oppure 'critical_region'.
    """
    return get_seed_signature(param, factor).region_type


def is_critical_region(param: int, factor: int) -> bool:
    """
    True se (param, factor) appartiene a una critical_region.
    """
    return get_region_type(param, factor) == "critical_region"


def is_canonical_critical_seed(param: int, factor: int) -> bool:
    """
    True solo per il seed canonico critico (qui (2,3)).
    """
    sig = get_seed_signature(param, factor)
    return sig.region_type == "critical_region" and sig.is_canonical_seed


def complexity_flavour(param: int, factor: int) -> str:
    """
    Mappa il tipo di regione in una 'flavour' di complessità:

      regular_region     -> 'P_like'
      precritical_region -> 'threshold_precritical'
      critical_region    -> 'NP_like'
    """
    region = get_region_type(param, factor)
    if region == "regular_region":
        return "P_like"
    if region == "critical_region":
        return "NP_like"
    return "threshold_precritical"


if __name__ == "__main__":
    print("=== Loventre Engine – Theory Bridge Seed demo ===\n")
    for param in (1, 2, 3):
        for factor in (1, 2, 3):
            sig = get_seed_signature(param, factor)
            flavour = complexity_flavour(param, factor)
            print(f"(param={param}, factor={factor})")
            print(f"  region_type        : {sig.region_type}")
            print(f"  pattern_short      : {sig.pattern_short}")
            print(f"  regime_1d_short    : {sig.regime_1d_short}")
            print(f"  regime_1d_long     : {sig.regime_1d_long}")
            print(f"  regime_multi_short : {sig.regime_multi_short}")
            print(f"  regime_multi_long  : {sig.regime_multi_long}")
            print(f"  spread_short       : {sig.spread_short}")
            print(f"  spread_long        : {sig.spread_long}")
            print(f"  multi_critical_long: {sig.multi_critical_long}")
            print(f"  is_canonical_seed  : {sig.is_canonical_seed}")
            print(f"  complexity_flavour : {flavour}")
            print("-" * 50)


# ================================================================
# Einstein–Loventre interpretive legend (layer di lettura)
# ================================================================

EINSTEIN_LOVENTRE_LEGEND = r"""
============================================================
EINSTEIN–LOVENTRE LEGEND – COME LEGGERE LE METRICHE
============================================================

Obiettivo
---------
Questa legenda collega le etichette meta_decision (P_like, NP_like_critico,
NP_like_black_hole, ecc.) e le famiglie critiche TSP_crit_n / SAT_crit_n
con i "layer" alla Einstein introdotti nel motore Loventre:

- spazio informazionale (curvatura κ, entropia H, potenziale U, barriera V0),
- tempo interno (p_tunnel, redshift_inf, gamma_dilation, time_regime),
- energia (E, E_min_for_p_target, energy_regime),
- massa informazionale (m_L, mass_mean, inertial_difficulty_index, mass_regime),
- geodetiche e caos (geodesic_deviation_index, geod_regime),
- orizzonti / buchi neri informazionali (horizon_detected, black_hole_risk).


1) Assi geometrici principali
-----------------------------

(1.a) Spazio informazionale
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
- Ogni history di stati Loventre è una traiettoria {C(s_t), H(s_t)} nel paesaggio
  interno del problema/istanza.
- Da C e H costruiamo:
    κ(s) = G_L · C(s) + λ_L
    U(s) = α · κ(s) + β · H(s)
- Fissando una soglia V0, definiamo la barriera di complessità:
    regione di barriera = { s : U(s) ≥ V0 }
  e misuriamo:
    - V0: altezza della barriera,
    - a_min: spessore minimo (in step) della regione di barriera,
    - barrier_occupancy: frazione di step della history passati nella barriera.

- La classificazione spaziale di base è:
    - regular      : paesaggio senza barriera seria o con V0 bassa rispetto a E,
    - precritical  : barriera presente ma ancora attaccabile,
    - critical     : barriera strutturata e alta, tipicamente NP_like-critica,
    - mixed        : regioni diverse coesistono lungo la history.


(1.b) Tempo interno e dilatazione
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
- La probabilità di tunneling creativo è (in forma base):
    p_tunnel ≈ exp(-2 · sqrt(max(V0 - E, 0)) · a_min)
- Il redshift informazionale è:
    redshift_inf = -ln(p_tunnel)         (per 0 < p_tunnel ≤ 1)
    gamma_dilation = 1 + redshift_inf    (con eventuale gamma_cap)
- Il regime temporale è:
    - time_euclidean  : gamma≈1–2 (tempo quasi piatto),
    - time_threshold  : gamma intermedio (zona di soglia),
    - time_hyperbolic : gamma grande (tempo fortemente dilatato).

- difficulty_index ≈ gamma_dilation · barrier_occupancy misura quanto il motore
  resta "intrappolato" in regioni di barriera con tempo interno dilatato.


(1.c) Energia
~~~~~~~~~~~~~
- E è il budget di energia/meta-risorse che il motore assegna all'istanza.
- E_min_for_p_target è l'energia minima necessaria per ottenere almeno p_target
  di successo (su un tentativo singolo) attraverso il tunneling.
- energy_regime è qualitativo:
    - no_barrier   : nessuna barriera significativa,
    - overpowered  : E >> E_min_for_p_target,
    - critical     : E ≈ E_min_for_p_target,
    - underpowered : E << E_min_for_p_target.

- P_success(N_budget) = 1 - (1 - p_tunnel)^N_budget è la probabilità cumulativa
  di successo entro N_budget tentativi meta.


(1.d) Massa informazionale e principio di equivalenza Loventre
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
- La massa informazionale per uno stato è:
    m_L(s) = m0 + w_C · C(s) + w_H · H(s)
- Su una history leggiamo:
    - mass_mean: media di m_L lungo gli step,
    - mass_max : massimo di m_L lungo gli step.

- L'indice inerziale è:
    inertial_difficulty_index ≈ difficulty_index · mass_mean
  e misura quanto la dilatazione del tempo, combinata con la massa, rende
  "pesante" la dinamica del motore.

- mass_regime (nelle meta-decisioni) o mass_regime_eff (nelle famiglie critiche)
  è tipicamente uno fra:
    - mass_light  : massa/massa_eff piccola,
    - mass_medium : massa intermedia,
    - mass_heavy  : massa pesante.

Interpretazione: come nella GR, la massa è sia sorgente di curvatura (via κ)
che fattore di inerzia: problemi con mass_heavy tendono ad avere barriere più
dure, tempi più dilatati e dinamiche quasi da buco nero.


(1.e) Geodetiche, lensing e caos geodetico
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
- Il motore Loventre può seguire geodetiche di complessità:
    L(s) ≈ a_geod · |κ(s)| + b_geod · H(s) + c_geod
  arricchite da massa e lensing (regioni attrattive/repulsive nel paesaggio).

- La deviazione geodetica fra due configurazioni (seed o istanze critiche
  successive) è riassunta da:
    geodesic_deviation_index  (scala [0,∞), tipicamente [0,1] nei lab)
- Dalla deviazione nasce geod_regime:
    - geod_stable     : piccole deviazioni (paesaggio liscio),
    - geod_transition : deviazioni intermedie,
    - geod_chaotic    : deviazioni grandi (forte sensibilità ai vicini).

Interpretazione: geod_chaotic indica una regione in cui piccoli cambiamenti
(param, factor oppure n) portano a geometrie molto diverse: "turbulenza"
informazionale nel senso Loventre.


(1.f) Orizzonti di complessità e buchi neri informazionali
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
- detect_complexity_horizon usa:
    - p_tunnel globale,
    - gamma_dilation,
    - inertial_difficulty_index,
    - barrier_occupancy,
    - finestra finale sugli U,
  per decidere se siamo in regime quasi da buco nero.

- Segnali chiave:
    horizon_detected = True
    black_hole_risk  = True

- In questa regione:
    - p_tunnel è praticamente zero (su scala macchina),
    - gamma_dilation è enorme,
    - l'occupazione vicino alla barriera è significativa,
    - la massa/inerzia è alta.
  La combinazione porta alla meta-label NP_like_black_hole.


2) Meta-label principali e loro lettura
---------------------------------------

Le meta-label combinano in modo qualitativo:
- classificazione spaziale (regular / precritical / critical),
- tempo interno (time_regime, gamma_dilation),
- energia (energy_regime),
- massa/inerzia (mass_regime, inertial_difficulty_index),
- orizzonte/buco nero (horizon_detected, black_hole_risk),
- struttura geodetica (geod_regime).


2.a) P_like_accessibile / P_like_like
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Tipico pattern delle metriche:
- classificazione spaziale: regular o precritical,
- p_tunnel non minuscolo (ad es. p_tunnel >> 10^{-4}),
- gamma_dilation ≈ 1–4 (time_euclidean o time_threshold),
- energy_regime: overpowered o critical,
- mass_regime: mass_light o mass_medium,
- nessun orizzonte, black_hole_risk=False,
- geod_regime: può variare (anche geod_chaotic), ma senza intrappolamento
  strutturale.

Interpretazione:
- Problemi/istanze "accessibili" con il budget corrente.
- In termini Loventre: la geometria non ostacola profondamente il motore.
- È la zona P-like nel senso operativo del motore: esiste un percorso con
  barriere gestibili e tempo interno non schiacciato.


2.b) zona_intermedia
~~~~~~~~~~~~~~~~~~~~
Tipico pattern:
- classificazione spaziale spesso critical, ma non estrema,
- p_tunnel piccolo ma non astronomicamente piccolo,
- gamma_dilation intermedio-alto (time_threshold o inizio time_hyperbolic),
- energy_regime: spesso underpowered, ma non catastrofico,
- mass_regime: tipicamente mass_medium,
- horizon_detected=False, black_hole_risk=False,
- geod_regime: transition o chaotico.

Interpretazione:
- Regione di frontiera fra P_like e NP_like_critico.
- Il motore può ancora "giocarsi la partita", ma ogni tentativo è costoso
  e soggetto a forte variabilità geodetica.
- In pratica: investimenti selettivi, non sistematici.


2.c) NP_like_critico / NP_like_critico_ma_esplorabile
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Tipico pattern:
- classificazione spaziale: critical,
- p_tunnel molto piccolo (tunneling raro ma non completamente azzerato),
- gamma_dilation alta (time_hyperbolic stabile),
- energy_regime: underpowered rispetto alla barriera attuale,
- mass_regime: spesso mass_medium o mass_heavy,
- horizon_detected può essere False (regime pre-black-hole),
- geod_regime: spesso geod_chaotic o geod_transition.

Interpretazione:
- Famiglie TSP_crit_n e SAT_crit_n mostrano proprio questa transizione:
  per n moderati otteniamo NP_like_critico con P_success modesto ma non nullo.
- NP_like_critico_ma_esplorabile (quando usato) indica casi in cui, pur essendo
  critica, la geometria consente ancora esperimenti non completamente disperati
  con N_budget non astronomici.
- È la regione chiave per evidenziare la separazione strutturale fra P_like
  e NP_like nel senso Loventre.


2.d) NP_like_black_hole
~~~~~~~~~~~~~~~~~~~~~~~
Tipico pattern:
- classificazione spaziale: critical,
- p_tunnel ≈ 0 su scala numerica (tunneling praticamente impossibile),
- gamma_dilation enorme (time_hyperbolic estremo),
- energy_regime: fortemente underpowered,
- mass_regime: tipicamente mass_heavy,
- horizon_detected=True, black_hole_risk=True,
- spesso E_min_for_p_target >> E disponibile,
- geod_regime: non necessariamente caotico (può essere anche "geod_stable")
  ma la barriera è così profonda che la dinamica è bloccata.

Interpretazione:
- È la versione Loventre di un buco nero informazionale.
- Le famiglie TSP_crit_n e SAT_crit_n, per n grandi, entrano in questo regime:
  P_success collassa anche per N_budget polinomiale, E[N] esplode, e la massa
  effettiva/inerzia segnala una dinamica quasi immobile.
- Qui il motore consiglia quasi sempre "MOLLA": investire ulteriormente risorse
  su queste istanze non è razionale con il budget attuale.


3) Regole di lettura veloci (mnemoniche)
----------------------------------------

- P_like_accessibile / P_like_like:
    regular/precritical + time_euclidean/threshold +
    energy_regime non underpowered +
    nessun orizzonte/buco-nero.

- zona_intermedia:
    critical ma senza orizzonte +
    time_threshold / inizio time_hyperbolic +
    energia e massa intermedie +
    p_tunnel piccolo ma non microscopico.

- NP_like_critico:
    critical + time_hyperbolic stabile +
    energia sotto-soglia +
    massa medio-pesante +
    tunneling raro ma non completamente spento.

- NP_like_black_hole:
    critical + horizon_detected=True + black_hole_risk=True +
    gamma enorme + p_tunnel≈0 +
    massa pesante (mass_heavy) +
    P_success che collassa con N_budget polinomiale.


Questa legenda non introduce nuove regole di codice, ma fornisce una mappa
mentale per leggere in modo coerente tutti i layer Einstein–Loventre che
compaiono nei lab:

- loventre_meta_decision_engine_lab.py
- loventre_meta_decision_cli.py
- loventre_meta_portfolio_lab.py
- loventre_tsp_critical_family_scaling.py
- loventre_sat_critical_family_scaling.py
- loventre_global_profile_lab.py
- loventre_geodesic_deviation_lab.py
- loventre_einstein_layers_test_lab.py

L'idea è che ogni meta_label non sia un'etichetta arbitraria, ma la sintesi
di uno "stato geometrico" completo (spazio, tempo, energia, massa, geodetiche,
orizzonti) del problema nel senso del Teorema / Motore di Loventre.
"""

def print_einstein_loventre_legend() -> None:
    """
    Stampa a schermo la legenda interpretativa Einstein–Loventre.
    Utile come promemoria rapido quando si guardano i report/atlanti.
    """
    print(EINSTEIN_LOVENTRE_LEGEND)

# ================================================================
# Quick summary Einstein–Loventre (lettura operativa veloce)
# ================================================================

from typing import Mapping, Any


def _extract_metric_str(metrics: Mapping[str, Any], key: str, default: str = "unknown") -> str:
    val = metrics.get(key, default)
    if val is None:
        return default
    return str(val)


def build_einstein_loventre_quick_summary_line(metrics: Mapping[str, Any]) -> str:
    """
    Costruisce una singola riga compatta con le principali etichette:
    meta_label, time_regime, energy_regime, mass_regime, geod_regime,
    eventuale orizzonte/buco-nero e strategia locale.
    """
    meta_label = _extract_metric_str(metrics, "meta_label", "?")
    time_regime = _extract_metric_str(metrics, "time_regime", "?")
    energy_regime = _extract_metric_str(metrics, "energy_regime", "unknown")

    mass_regime = (
        metrics.get("mass_regime")
        or metrics.get("mass_regime_eff")
        or "unknown"
    )
    geod_regime = (
        metrics.get("geod_regime")
        or metrics.get("geod_regime_eff")
        or "unknown"
    )

    horizon = bool(metrics.get("horizon_detected", False))
    black_hole = bool(metrics.get("black_hole_risk", False))

    strategy = (
        metrics.get("strategy")
        or metrics.get("strategy_local")
        or metrics.get("strategy_label")
        or ""
    )

    parts = [
        f"meta={meta_label}",
        f"time={time_regime}",
        f"energy={energy_regime}",
        f"mass={mass_regime}",
        f"geod={geod_regime}",
    ]

    if black_hole:
        parts.append("black_hole=True")
    elif horizon:
        parts.append("near_horizon=True")

    if strategy:
        parts.append(f"strategy={strategy}")

    return " | ".join(parts)


def build_einstein_loventre_quick_explanation(metrics: Mapping[str, Any]) -> str:
    """
    Restituisce 1–3 frasi operative in stile:
    - "Regime P_like..."
    - "Regime NP_like-critico..."
    - "Regime NP_like black-hole..."
    """
    meta_label = _extract_metric_str(metrics, "meta_label", "").strip()
    energy_regime = _extract_metric_str(metrics, "energy_regime", "").strip()
    time_regime = _extract_metric_str(metrics, "time_regime", "").strip()
    mass_regime = (
        metrics.get("mass_regime")
        or metrics.get("mass_regime_eff")
        or ""
    )
    mass_regime = str(mass_regime).strip()

    black_hole = bool(metrics.get("black_hole_risk", False))
    horizon = bool(metrics.get("horizon_detected", False))

    # Caso buco nero informazionale
    if black_hole or meta_label.startswith("NP_like_black_hole"):
        return (
            "Regime NP_like black-hole Loventre: barriera estremamente profonda, "
            "p_tunnel≈0, tempo interno fortemente time_hyperbolic e massa pesante. "
            "Interpretazione operativa: il motore considera irrazionale investire "
            "ulteriori risorse su questa istanza con il budget attuale (MOLLA salvo "
            "motivi esterni molto forti)."
        )

    # Caso P-like / accessibile
    if meta_label.startswith("P_like"):
        return (
            "Regime P_like / accessibile: geometria favorevole o gestionibile, "
            "tempo interno non eccessivamente dilatato e nessun orizzonte di complessità. "
            "Interpretazione operativa: investimento raccomandato, strategia INSISTI "
            "finché non cambiano le condizioni energetiche."
        )

    # Zona intermedia
    if meta_label.startswith("zona_intermedia"):
        return (
            "Regime Loventre intermedio: istanza al confine fra accessibile e critica. "
            "Tempo interno spesso time_threshold o time_hyperbolic moderato, energia "
            "tipicamente underpowered e massa intermedia. "
            "Interpretazione operativa: investire solo in modo selettivo; "
            "CAMBIA_STRATEGIA o limita il budget se non compaiono segnali migliorativi."
        )

    # NP_like-critico senza buco nero
    if meta_label.startswith("NP_like_critico"):
        if energy_regime == "overpowered":
            return (
                "Regime NP_like-critico ma con energia sovrabbondante: la struttura "
                "geometrica è dura, ma il budget energetico attuale permette ancora "
                "un'esplorazione aggressiva. Interpretazione operativa: esperimenti "
                "mirati possibili, ma monitorare attentamente consumo energetico "
                "e time_regime."
            )
        return (
            "Regime NP_like-critico Loventre: barriera alta, tempo interno "
            f"{time_regime} e energia in regime {energy_regime or 'underpowered'}. "
            "La massa informazionale ("
            f"{mass_regime or 'sconosciuta'}"
            ") amplifica l'inerzia. "
            "Interpretazione operativa: casi da trattare come fortemente rischiosi; "
            "CAMBIA_STRATEGIA o MOLLA a meno di motivazioni strategiche specifiche."
        )

    # Fallback generico
    if horizon:
        return (
            "Regime vicino a orizzonte di complessità: la dinamica mostra segni di "
            "intrappolamento e forte dilatazione del tempo interno, pur senza essere "
            "ancora in pieno buco nero Loventre. Interpretazione operativa: grande "
            "prudenza, tendi a ridurre il budget o a modificare la strategia."
        )

    return (
        "Regime Loventre non classificato in uno dei casi canonici, oppure meta_label "
        "non riconosciuta. Interpretazione operativa: rileggi le metriche complete "
        "e la legenda Einstein–Loventre per una diagnosi più fine."
    )


def print_einstein_loventre_quick_summary(metrics: dict) -> None:
    """
    Riassunto compatto Einstein–Loventre in due strati:
      - linea sintetica rischio / meta / tempo / energia / massa / geod / strategia,
      - opzionale warning Schwarzschild–Loventre (near-horizon / supercritical).
    """
    meta = str(metrics.get("meta_label", "?"))
    time_regime = str(metrics.get("time_regime", "unknown"))
    energy_regime = str(metrics.get("energy_regime", "unknown"))
    mass_regime = str(metrics.get("mass_regime", "unknown"))
    geod_regime = str(metrics.get("geod_regime", "unknown"))

    strategy = str(
        metrics.get("strategy")
        or metrics.get("local_strategy")
        or metrics.get("decision_label")
        or "?"
    )

    risk = float(metrics.get("risk_index", 0.0) or 0.0)
    risk_class = str(metrics.get("risk_class", "UNKNOWN")).upper()
    bucket_map = {"LOW": "basso", "MEDIUM": "medio", "HIGH": "alto"}
    bucket = bucket_map.get(risk_class, risk_class.lower())

    line = (
        f"risk≈{risk:.1f}/10 ({bucket}) | "
        f"meta={meta} | time={time_regime} | energy={energy_regime} | "
        f"mass={mass_regime} | geod={geod_regime} | strategy={strategy}"
    )
    print(line)

    # Strato Schwarzschild–Loventre (se disponibile)
    schw_regime = metrics.get("schwarzschild_regime")
    if schw_regime:
        try:
            chi = float(metrics.get("schwarzschild_compactness", 0.0) or 0.0)
        except (TypeError, ValueError):
            chi = 0.0
        try:
            gamma_schw = float(metrics.get("gamma_dilation_schwarzschild", 1.0) or 1.0)
        except (TypeError, ValueError):
            gamma_schw = 1.0

        schw_regime_str = str(schw_regime)

        if schw_regime_str == "NEAR_HORIZON":
            print(
                f"Warning Schwarzschild–Loventre: regione vicino all'orizzonte "
                f"(χ≈{chi:.3f}, γ_schw≈{gamma_schw:.2f})."
            )
        elif schw_regime_str == "SUPERCRITICAL":
            print(
                f"ATTENZIONE Schwarzschild–Loventre: regione supercritica / oltre l'orizzonte "
                f"(χ≈{chi:.3f}, γ_schw≈{gamma_schw:.2f})."
            )
        # per SUBCRITICAL non stampiamo nulla di extra

def compute_einstein_loventre_risk_index(metrics: Mapping[str, Any]) -> float:
    """
    Costruisce un indice di rischio Einstein–Loventre in [0,10].

    Usa:
      - p_tunnel (più è piccolo, più rischio),
      - gamma_dilation (tempo iperbolico = rischio),
      - inertial_difficulty_index (massa * dilatazione),
      - horizon_detected / black_hole_risk,
      - meta_label / energy_regime per piccoli aggiustamenti coerenti.
    """
    # p_tunnel -> redshift informazionale
    try:
        p = float(metrics.get("p_tunnel", 0.0) or 0.0)
    except (TypeError, ValueError):
        p = 0.0

    if p <= 0.0:
        p_clamped = 1e-300
    else:
        p_clamped = max(min(p, 1.0), 1e-300)

    redshift = -math.log(p_clamped)          # ~0 se p≈1, grande se p è microscopico
    r_p = min(redshift / 10.0, 1.0)          # normalizzazione morbida

    # gamma_dilation
    try:
        gamma = float(metrics.get("gamma_dilation", 1.0) or 1.0)
    except (TypeError, ValueError):
        gamma = 1.0
    gamma_exc = max(gamma - 1.0, 0.0)
    r_gamma = min(gamma_exc / 10.0, 1.0)     # gamma≈11 -> r_gamma≈1

    # inerzia
    try:
        inert = float(metrics.get("inertial_difficulty_index", 0.0) or 0.0)
    except (TypeError, ValueError):
        inert = 0.0
    r_inert = min(inert / 20.0, 1.0)         # saturazione intorno a ~20

    # orizzonte / rischio buco nero
    horizon = bool(metrics.get("horizon_detected")) or bool(metrics.get("black_hole_risk"))
    r_hor = 1.0 if horizon else 0.0

    # combinazione di base
    base = 0.4 * r_p + 0.25 * r_gamma + 0.25 * r_inert + 0.10 * r_hor

    label = str(metrics.get("meta_label", "") or "")
    energy_reg = str(metrics.get("energy_regime", "") or "")

    # Aggiustamenti coerenti con le etichette meta
    if label.startswith("P_like"):
        # P-like: rischio massimo moderato, e ancora più basso se non underpowered
        base = min(base, 0.35)
        if energy_reg != "underpowered":
            base *= 0.7
    elif "zona_intermedia" in label:
        base = max(base, 0.4)
    elif "NP_like_critico" in label:
        base = max(base, 0.7)
    elif "NP_like_black_hole" in label:
        base = 1.0

    base = max(0.0, min(base, 1.0))
    return round(10.0 * base, 1)


def classify_einstein_loventre_risk(risk_index: float) -> str:
    """
    Traduce l'indice [0,10] in fasce qualitative:
      - basso, moderato, alto, estremo.
    """
    if risk_index < 2.0:
        return "basso"
    if risk_index < 4.0:
        return "moderato"
    if risk_index < 7.0:
        return "alto"
    return "estremo"


def build_einstein_loventre_quick_summary_line(metrics: Mapping[str, Any]) -> str:
    """
    Versione aggiornata: include l'indice di rischio Einstein–Loventre.
    Esempio:
      risk≈6.8/10 (alto) | meta=... | time=... | ...
    """
    risk = compute_einstein_loventre_risk_index(metrics)
    risk_bucket = classify_einstein_loventre_risk(risk)

    meta = str(metrics.get("meta_label", "unknown") or "unknown")
    time_regime = str(metrics.get("time_regime", "unknown") or "unknown")
    energy_regime = str(metrics.get("energy_regime", "unknown") or "unknown")

    mass_regime = metrics.get("mass_regime", None)
    if not mass_regime:
        mass_regime = metrics.get("mass_regime_eff", "unknown")
    mass_regime = str(mass_regime or "unknown")

    geod_regime = str(metrics.get("geod_regime", "unknown") or "unknown")
    strategy = str(
        metrics.get("local_strategy", metrics.get("decision_label", "?")) or "?"
    )

    return (
        f"risk≈{risk:.1f}/10 ({risk_bucket}) | "
        f"meta={meta} | time={time_regime} | energy={energy_regime} | "
        f"mass={mass_regime} | geod={geod_regime} | strategy={strategy}"
    )

# === Ponte teorico P-like vs NP_like-critico tramite K_globale ===

K_GLOBALE_THEORETICAL_SUMMARY = """
Nel modello Loventre toy attuale, il campo adattivo multifamiglia definisce
una curvatura informazionale globale K_globale ∈ [0,1] per famiglie di istanze
(seed_grid, TSP_crit_n, SAT_crit_n). Operativamente K_globale pesa tre ingredienti:
(i) il rischio medio Einstein–Loventre (risk_mean/10), (ii) la frazione di tempo
interno in regime time_hyperbolic, (iii) la massa informazionale effettiva
normalizzata (mass_eff/3).

Per la griglia di seed P-like il valore stimato è K_globale ≈ 0.3: la varietà
informazionale è quasi euclidea, con rischio basso, tempo prevalentemente
euclideo/threshold e massa moderata. Per le famiglie critiche TSP_crit_n e
SAT_crit_n K_globale si stabilizza intorno a ≈ 0.7: la curvatura diventa
fortemente negativa, con rischio elevato, dinamica quasi sempre time_hyperbolic
e massa più pesante, in un regime quasi da buco nero Loventre.

In questo senso K_globale fornisce un ponte geometrico fra P-like e
NP_like-critico: muovendosi dalla regione seed_grid alle famiglie TSP_crit_n /
SAT_crit_n si osserva una transizione di fase di curvatura informazionale, che
prepara il terreno per una futura formalizzazione del Teorema di Loventre in
termini di separazione fra varietà quasi-euclidee e regioni a curvatura critica.
"""

def print_k_globale_theory_summary() -> None:
    """
    Stampa un riassunto teorico (stile tesi) sul ruolo di K_globale.

    Utile per copiare/incollare in appunti o bozze di tesi senza dover
    ricostruire ogni volta la legenda concettuale.
    """
    print(K_GLOBALE_THEORETICAL_SUMMARY.strip())
# === Tabella riassuntiva famiglie P-like / NP_like-critiche ===

K_GLOBALE_FAMILY_TABLE = """
Tabella 1.x – Profilo Einstein–Loventre delle famiglie P-like e NP_like-critiche
(secondo il campo adattivo multifamiglia).

+------------+-----------+------------+-----------+-----------+----------+
| Famiglia   | risk_mean | time_hyp % | mass_eff  | K_globale | policy   |
+------------+-----------+------------+-----------+-----------+----------+
| seed_grid  |    1.52   |    22.2    |   2.05    |   0.28    | INSISTI  |
| TSP_crit_n |    6.11   |    83.3    |   2.40    |   0.72    | RITIRA   |
| SAT_crit_n |    5.98   |    83.3    |   2.30    |   0.70    | RITIRA   |
+------------+-----------+------------+-----------+-----------+----------+

Legenda:
  - risk_mean   : rischio Einstein–Loventre medio (0–10) per la famiglia.
  - time_hyp %  : percentuale di istanze in regime time_hyperbolic.
  - mass_eff    : massa informazionale effettiva media.
  - K_globale   : curvatura informazionale globale (0 ≈ P-like, 1 ≈ NP_like-critico).
  - policy      : linea guida del campo adattivo (INSISTI / ESPLORA / RITIRA).
"""

def print_k_globale_family_table() -> None:
    """Stampa la tabella riassuntiva delle famiglie P-like / NP_like-critiche."""
    print(K_GLOBALE_FAMILY_TABLE.strip())
