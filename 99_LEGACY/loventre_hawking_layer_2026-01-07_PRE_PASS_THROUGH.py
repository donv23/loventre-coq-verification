"""
loventre_hawking_layer.py

Strato Hawking–Loventre: definisce una 'temperatura informazionale'
T_H_L per l'orizzonte di complessità, basata su massa, compattezza
Schwarzschild e regime Planck.
"""

from __future__ import annotations

from typing import Any, Dict, Optional


def _safe_float(value: Any, default: float = 0.0) -> float:
    """Converte in float in modo robusto."""
    try:
        if value is None:
            return default
        return float(value)
    except Exception:
        return default


def _planck_weight(planck_regime: Optional[str]) -> float:
    """Peso [0,1] in base al regime Planck–Loventre."""
    if not planck_regime:
        return 0.0
    regime = str(planck_regime).lower()
    if regime in ("classical", "classico"):
        return 0.1
    if regime in ("semi_quantum", "semi-quantum", "semiquantum"):
        return 0.4
    if regime in ("meso_planck", "mesoplanck", "meso-planck"):
        return 0.7
    if regime in ("planckian", "ultra_planck", "planck"):
        return 1.0
    # default prudente
    return 0.3


def compute_hawking_temperature_from_metrics(metrics: Dict[str, Any]) -> float:
    """Calcola una temperatura informazionale T_H_L in [0,1].

    Linee guida:
    - buchi neri più leggeri -> temperatura più alta;
    - maggiore compattezza χ -> temperatura leggermente più alta;
    - regimi più planckiani -> temperatura più alta;
    - se le correzioni planckiane sopprimono molto il tunneling,
      la temperatura effettiva viene ridotta.
    """
    if not isinstance(metrics, dict):
        return 0.0

    # Massa effettiva (preferiamo mass_eff se presente, altrimenti mass_mean)
    mass_eff = metrics.get("mass_eff")
    if mass_eff is None:
        mass_eff = metrics.get("mass_mean")
    m = _safe_float(mass_eff, default=1.0)

    # fattore massa: piccoli m -> ~1, grandi m -> ~0
    mass_term = 1.0 / (1.0 + max(m, 0.0))

    # compattezza Schwarzschild χ
    chi = _safe_float(metrics.get("schwarzschild_compactness"), default=0.0)
    # mappiamo χ>=0 in [0,1) con una saturazione dolce
    chi_term = chi / (1.0 + abs(chi))

    # peso del regime Planck
    planck_term = _planck_weight(metrics.get("planck_regime"))

    # termine "leak" basato sul rapporto tra p_tunnel_planck e p_tunnel classico
    p_classic = _safe_float(metrics.get("p_tunnel"), default=0.0)
    p_planck = _safe_float(metrics.get("planck_p_tunnel_eff"), default=0.0)
    leak_term = 0.0
    if p_classic > 0.0 and p_planck >= 0.0:
        ratio = max(0.0, min(1.0, p_planck / max(p_classic, 1e-12)))
        # se le correzioni Planck sopprimono molto il tunneling (ratio<<1) -> buco nero più freddo
        # prendiamo sqrt per attenuare l'effetto
        leak_term = ratio ** 0.5

    # combinazione lineare pesata, poi clamp in [0,1]
    raw = (
        0.5 * mass_term
        + 0.2 * chi_term
        + 0.2 * planck_term
        + 0.1 * leak_term
    )

    if raw < 0.0:
        return 0.0
    if raw > 1.0:
        return 1.0
    return raw


def enrich_metrics_with_hawking_layer(
    metrics: Dict[str, Any], overwrite: bool = False
) -> Dict[str, Any]:
    """Arricchisce il dict metrics con T_H_L e un'etichetta di regime Hawking.

    Aggiunge:
    - hawking_T_L: temperatura informazionale in [0,1];
    - hawking_regime: 'cold_black' / 'metastable' / 'evaporating';
    - hawking_summary: breve descrizione testuale.

    Se overwrite=False, non sovrascrive chiavi esistenti.
    """
    if not isinstance(metrics, dict):
        return metrics

    if (not overwrite) and "hawking_T_L" in metrics:
        return metrics

    T_H_L = compute_hawking_temperature_from_metrics(metrics)

    # Determiniamo il regime Hawking tenendo conto anche del meta_label / black_hole_risk
    meta_label = str(metrics.get("meta_label", "") or "").lower()
    is_black = bool(metrics.get("black_hole_risk")) or ("black_hole" in meta_label)
    is_crit = ("np_like_critico" in meta_label) or ("zona_intermedia" in meta_label)

    if T_H_L < 0.25:
        regime = "cold_black"
    elif T_H_L < 0.65:
        regime = "metastable"
    else:
        regime = "evaporating"

    # Piccola correzione semantica: se non siamo in regime critico/nero, usiamo 'metastable' come default freddo
    if not (is_black or is_crit):
        if T_H_L < 0.3:
            regime = "metastable"

    if regime == "cold_black":
        summary = (
            f"buco nero informazionale freddo (T_H_L≈{T_H_L:.2f}): "
            "il campo NP_like appare stagnante, con canali di fuga molto deboli."
        )
    elif regime == "evaporating":
        summary = (
            f"buco nero informazionale caldo (T_H_L≈{T_H_L:.2f}): "
            "sotto pressione energetica il rischio può evaporare in modo significativo."
        )
    else:
        summary = (
            f"regime Hawking metastabile (T_H_L≈{T_H_L:.2f}): "
            "campo NP_like con canali di fuga presenti ma non dominanti."
        )

    metrics = dict(metrics)
    metrics.setdefault("hawking_T_L", T_H_L)
    metrics.setdefault("hawking_regime", regime)
    metrics.setdefault("hawking_summary", summary)

    return metrics


def compute_hawking_layer(metrics: Dict[str, Any]) -> Dict[str, Any]:
    """
    Entry point usato dal Loventre Engine per lo Strato Hawking–Loventre.

    - Arricchisce metrics con i campi hawking_*
    - Appende una sezione dedicata a meta_explanation, seguendo il pattern
      degli altri strati (massa, Schwarzschild, Planck).
    """
    if not isinstance(metrics, dict):
        return metrics

    metrics = enrich_metrics_with_hawking_layer(metrics, overwrite=False)

    base_expl = str(metrics.get("meta_explanation", "") or "").rstrip()
    hawking_summary = metrics.get("hawking_summary")
    snippet = ""
    if hawking_summary:
        snippet = str(hawking_summary)

    if snippet:
        if base_expl:
            metrics["meta_explanation"] = (
                base_expl
                + "\n\n- Strato Hawking–Loventre:\n  "
                + snippet
            )
        else:
            metrics["meta_explanation"] = "- Strato Hawking–Loventre:\n  " + snippet

    return metrics


if __name__ == "__main__":
    # Piccolo smoke-test locale su un dizionario fittizio
    toy = {
        "mass_mean": 2.0,
        "schwarzschild_compactness": 1.1,
        "planck_regime": "meso_planck",
        "p_tunnel": 1e-3,
        "planck_p_tunnel_eff": 5e-4,
        "meta_label": "NP_like_critico",
        "black_hole_risk": False,
    }
    enriched = enrich_metrics_with_hawking_layer(toy, overwrite=True)
    print("hawking_T_L    =", enriched.get("hawking_T_L"))
    print("hawking_regime =", enriched.get("hawking_regime"))
    print("hawking_summary:")
    print(enriched.get("hawking_summary"))

# === Loventre Hawking UV layer (seed v1) =====================================

def compute_hawking_uv_regime(metrics: dict) -> dict:
    """
    Calcola una piccola firma UV (ultraviolet) sullo stato Hawking a partire dal
    bus centrale `metrics`. Non modifica il dict, restituisce solo un nuovo dict
    con chiavi:
      - 'hawking_uv_index'
      - 'hawking_uv_phase'
      - 'hawking_uv_energy'
      - 'hawking_uv_comment'
    La combinazione è volutamente semplice ma stabile, pensata come primo seed
    per un layer UV curvato.
    """
    if metrics is None:
        raise ValueError("metrics must not be None")

    kappa = float(metrics.get("kappa_eff", 0.0) or 0.0)
    entropy = float(metrics.get("entropy_eff", 0.0) or 0.0)
    V0 = float(metrics.get("V0", 0.0) or 0.0)
    p_tunnel = float(metrics.get("p_tunnel", 0.0) or 0.0)
    risk = float(metrics.get("risk_index", 0.0) or 0.0)

    # combinazione seed: norma euclidea (kappa, entropy) + contributo di barriera
    uv_energy = (kappa ** 2 + entropy ** 2) ** 0.5 + 0.1 * V0

    # indice UV amplificato da tunneling e rischio
    uv_index = uv_energy * (1.0 + 0.5 * p_tunnel + 0.25 * risk)

    # discretizza uv_index in tre fasi qualitative
    if uv_index < 1.0:
        phase = "sub_uv"
        comment = "regime Hawking sotto–curvatura UV"
    elif uv_index < 3.0:
        phase = "critical_uv"
        comment = "regime Hawking UV quasi–critico"
    else:
        phase = "trans_uv"
        comment = "regime Hawking UV trans–critico"

    return {
        "hawking_uv_index": uv_index,
        "hawking_uv_phase": phase,
        "hawking_uv_energy": uv_energy,
        "hawking_uv_comment": comment,
    }


def append_hawking_uv_layer_to_metrics(metrics: dict) -> dict:
    """
    Arricchisce il bus `metrics` con la firma Hawking UV.

    - È safe: se le chiavi UV esistono già, non le tocca (idempotente).
    - Opera in-place ma restituisce comunque `metrics` per chaining.
    - Non modifica nessuna delle chiavi pre-esistenti usate dal motore.
    """
    if metrics is None:
        raise ValueError("metrics must not be None")

    if "hawking_uv_index" in metrics and "hawking_uv_phase" in metrics:
        return metrics

    uv = compute_hawking_uv_regime(metrics)
    metrics.update(uv)
    return metrics
