#!/usr/bin/env python3
"""
Patch: aggiunge la funzione loventre_global_decision(...) a
loventre_meta_decision_engine.py, se non esiste già.

Idempotente: se la funzione è già presente, non fa nulla.
"""

from pathlib import Path
import ast
import textwrap


TARGET = Path("loventre_meta_decision_engine.py")


def main() -> None:
    if not TARGET.exists():
        raise SystemExit(f"{TARGET} non trovato.")

    src = TARGET.read_text(encoding="utf-8")

    if "def loventre_global_decision(" in src:
        print("loventre_meta_decision_engine.py ha già loventre_global_decision(). Nessuna modifica.")
        return

    func_code = '''
def loventre_global_decision(metrics: Metrics, family: str | None = None) -> Metrics:
    """
    Decisione Loventre globale a partire da un dizionario di metriche.

    Input:
      - metrics: dict prodotto da meta_decide_instance_with_mass,
                 meta_analyze_seed, TSP_crit_n, SAT_crit_n, ecc.
      - family : etichetta opzionale per la famiglia (es. 'seed_grid',
                 'TSP_crit_n', 'SAT_crit_n', 'SAT_toy', ...).

    Output:
      - nuovo dict che estende metrics con:
          * global_decision: 'INSISTI' / 'VALUTA' / 'RITIRA'
          * global_color   : 'GREEN' / 'AMBER' / 'RED'
          * global_label   : etichetta compatta ('Loventre_GREEN', ecc.)
          * global_score   : score in [0,1] (successo penalizzato da rischio/tempo)
          * loventre_global_explanation: spiegazione testuale compatta
    """
    base: Metrics = dict(metrics)  # copia difensiva

    # --- 1) Profilo di rischio (se manca, lo costruiamo ora) ---
    risk_profile = base.get("risk_profile")
    if not isinstance(risk_profile, dict) or "risk_index" not in risk_profile:
        try:
            risk_profile = _compute_risk_profile(base)
        except Exception:
            # Fallback minimale: usiamo solo risk_index / risk_class se presenti
            try:
                risk_index_raw = float(base.get("risk_index", 0.0) or 0.0)
            except Exception:
                risk_index_raw = 0.0
            risk_profile = {
                "risk_index": risk_index_raw,
                "risk_class": str(base.get("risk_class", "LOW") or "LOW"),
                "horizon_flag": bool(base.get("horizon_detected", False)),
                "black_hole_flag": bool(base.get("black_hole_risk", False)),
            }

    try:
        risk_index = float(risk_profile.get("risk_index", base.get("risk_index", 0.0)) or 0.0)
    except Exception:
        risk_index = 0.0

    risk_class = str(risk_profile.get("risk_class", base.get("risk_class", "LOW")) or "LOW")
    horizon_flag = bool(risk_profile.get("horizon_flag", base.get("horizon_detected", False)))
    black_hole_flag = bool(risk_profile.get("black_hole_flag", base.get("black_hole_risk", False)))

    base["risk_profile"] = risk_profile
    base["risk_index"] = risk_index
    base["risk_class"] = risk_class
    base.setdefault("horizon_detected", horizon_flag)
    base.setdefault("black_hole_risk", black_hole_flag)

    # --- 2) Etichette di regione / NP-like / tempo / meta ---
    classification = str(base.get("classification") or "").lower()
    region_raw = base.get("region_label") or base.get("region") or classification or "unknown"
    region_label = str(region_raw).upper()

    np_like_label_raw = base.get("np_like_label") or ""
    np_like_label = str(np_like_label_raw).upper()

    time_regime = str(base.get("time_regime", "time_euclidean") or "time_euclidean")
    meta_label = str(base.get("meta_label", "") or "")
    strategy = base.get("policy_strategy") or base.get("strategy") or ""

    # --- 3) Quantità numeriche chiave ---
    try:
        p_tunnel = float(base.get("p_tunnel", 0.0) or 0.0)
    except Exception:
        p_tunnel = 0.0

    try:
        gamma_dil = float(base.get("gamma_dilation", 1.0) or 1.0)
    except Exception:
        gamma_dil = 1.0
    if gamma_dil < 1.0:
        gamma_dil = 1.0

    # P_success base se disponibile (TSP_crit_n, SAT_crit_n, meta-portfolio, ecc.)
    try:
        base_success = float(
            base.get("P_success", base.get("p_success", 0.0)) or 0.0
        )
    except Exception:
        base_success = 0.0

    if base_success <= 0.0 and p_tunnel > 0.0:
        # Approssimazione morbida: successo meta su ~10 tentativi indipendenti.
        try:
            base_success = 1.0 - (1.0 - p_tunnel) ** 10
        except Exception:
            base_success = p_tunnel

    # --- 4) Flag NP_like critico/black_hole (grossolani ma stabili) ---
    is_np_like = False
    if np_like_label:
        is_np_like = np_like_label.startswith("NP")
    elif meta_label.startswith("NP_like"):
        is_np_like = True
    else:
        if classification == "critical" and time_regime == "time_hyperbolic":
            is_np_like = True

    # --- 5) Penalizzazioni (rischio, tempo, NP_like) ---
    # Rischio: risk_index in [0,10] -> fattore in [0.2,1.0]
    r_clamped = max(0.0, min(10.0, risk_index))
    risk_penalty = 1.0 - 0.08 * r_clamped
    if risk_penalty < 0.1:
        risk_penalty = 0.1

    # Tempo interno
    if time_regime == "time_hyperbolic":
        time_penalty = 0.5
    elif time_regime == "time_threshold":
        time_penalty = 0.8
    else:
        time_penalty = 1.0

    # NP_like penalty
    np_penalty = 0.7 if is_np_like else 1.0

    global_score = base_success * risk_penalty * time_penalty * np_penalty
    if global_score < 0.0:
        global_score = 0.0
    if global_score > 1.0:
        global_score = 1.0

    # --- 6) Decisione finale (GREEN / AMBER / RED) ---
    if black_hole_flag or (
        is_np_like
        and (risk_class in ("HIGH", "BLACK_HOLE") or gamma_dil >= 10.0)
    ):
        global_color = "RED"
        global_decision = "RITIRA"
    elif global_score >= 0.7 and risk_class in ("LOW", "MEDIUM") and not is_np_like:
        global_color = "GREEN"
        global_decision = "INSISTI"
    elif global_score <= 0.15 or (
        risk_class in ("HIGH", "BLACK_HOLE") and gamma_dil >= 5.0
    ):
        global_color = "RED"
        global_decision = "RITIRA"
    elif global_score <= 0.4 or risk_class == "MEDIUM" or is_np_like:
        global_color = "AMBER"
        global_decision = "VALUTA"
    else:
        global_color = "GREEN"
        global_decision = "INSISTI"

    if global_decision == "INSISTI":
        global_label = "Loventre_GREEN"
    elif global_decision == "VALUTA":
        global_label = "Loventre_AMBER"
    else:
        global_label = "Loventre_RED"

    # --- 7) Spiegazione compatta ---
    explanation_lines: List[str] = []

    if family:
        explanation_lines.append(f"Famiglia Loventre: {family}.")

    explanation_lines.append(
        f"region_label={region_label}, time_regime={time_regime}, meta_label={meta_label or 'N/A'}."
    )
    explanation_lines.append(
        f"risk_class={risk_class}, risk_index≈{risk_index:.2f}."
    )
    explanation_lines.append(
        f"p_tunnel≈{p_tunnel:.3e}, base_success≈{base_success:.3e}, global_score≈{global_score:.3f}."
    )

    if is_np_like:
        explanation_lines.append(
            "Firma NP_like-critica nel senso Loventre (regime critico/iperbolico)."
        )
    if black_hole_flag:
        explanation_lines.append(
            "Regime vicino al buco nero informazionale (horizon / black_hole attivi)."
        )
    if strategy:
        explanation_lines.append(f"Strategia locale/bridge: {strategy}.")

    loventre_expl = "\\n".join(explanation_lines)

    summary = {
        "global_decision": global_decision,
        "global_color": global_color,
        "global_label": global_label,
        "global_score": global_score,
        "region_label": region_label,
        "np_like_flag": is_np_like,
        "np_like_label": base.get("np_like_label"),
        "risk_index": risk_index,
        "risk_class": risk_class,
        "time_regime": time_regime,
        "meta_label": meta_label,
        "horizon_detected": bool(base.get("horizon_detected", horizon_flag)),
        "black_hole_risk": bool(base.get("black_hole_risk", black_hole_flag)),
        "strategy": strategy,
        "family": family,
        "loventre_global_explanation": loventre_expl,
    }

    result: Metrics = dict(base)
    result.update(summary)
    return result
'''

    func_code = textwrap.dedent(func_code)

    new_src = src.rstrip() + "\n\n\n" + func_code

    # Verifica sintassi prima di scrivere
    try:
        ast.parse(new_src)
    except SyntaxError as e:
        raise SystemExit(f"Errore di sintassi dopo la patch: {e}") from e

    TARGET.write_text(new_src, encoding="utf-8")
    print("loventre_meta_decision_engine.py aggiornato con loventre_global_decision().")


if __name__ == "__main__":
    main()

