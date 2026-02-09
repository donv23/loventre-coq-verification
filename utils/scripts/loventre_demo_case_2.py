#!/usr/bin/env python3
"""
loventre_demo_case_2.py

Demo end-to-end Loventre – Scenario di frontiera UV

1. Costruisce un metrics di core Loventre + massa (seed sintetico più "spinto").
2. Scatta uno snapshot *_base del core (se l'helper esiste).
3. Passa in sequenza per i layer del meta–engine:
   - append_schwarzschild_layer_to_metrics
   - append_hawking_layer_to_metrics
   - append_planck_layer_to_metrics
   - apply_policy_bridge_to_metrics
   - append_policy_bridge_to_metrics
4. Forza un regime Hawking UV di "frontiera" (trans_uv con indice alto) sul metrics,
   in modo che il Policy Bridge lo incorpori in risk_index e policy.
5. Stampa un mini–report leggibile da umano.
"""

import sys
import pathlib


def import_meta_engine():
    """Aggancia la root del progetto e importa loventre_meta_decision_engine."""
    root = pathlib.Path(__file__).resolve().parents[1]
    if str(root) not in sys.path:
        sys.path.insert(0, str(root))

    try:
        import loventre_meta_decision_engine as lmd  # type: ignore
    except Exception as e:
        print("[ERROR] Impossibile importare loventre_meta_decision_engine:", e)
        print("sys.path attuale:")
        for p in sys.path:
            print("  -", p)
        sys.exit(1)
    return lmd


def build_frontier_core_metrics():
    """
    Costruisce un core Loventre sintetico in una regione "più critica",
    pensata come candidato per un regime di frontiera UV.
    """
    metrics = {
        "instance_id": "DEMO-CASE-2",
        "instance_label": "Loventre demo case 2 – scenario di frontiera UV",
        "kappa_eff": 1.4,
        "entropy_eff": 2.7,
        "V0": 3.4,
        "p_tunnel": 0.38,
        "mass_mean": 1.9,
        "chi": 0.5,
        # rischio di partenza più alto rispetto al case 1
        "risk_index": 3.6,
    }
    return metrics


def run_pipeline_frontier(lmd, metrics):
    """
    Esegue la pipeline Loventre sui metrics sintetici, usando i layer
    disponibili nel meta–engine e forzando un regime Hawking UV di frontiera.
    """
    # 1. Snapshot baseline del core, se l'helper esiste
    if hasattr(lmd, "_snapshot_loventre_core_baseline"):
        try:
            metrics = lmd._snapshot_loventre_core_baseline(metrics)  # type: ignore[attr-defined]
        except Exception as e:
            print("[WARN] _snapshot_loventre_core_baseline ha sollevato un'eccezione:", repr(e))

    # 2. Schwarzschild layer
    if hasattr(lmd, "append_schwarzschild_layer_to_metrics"):
        try:
            metrics = lmd.append_schwarzschild_layer_to_metrics(metrics)  # type: ignore[attr-defined]
        except Exception as e:
            print("[WARN] append_schwarzschild_layer_to_metrics ha sollevato un'eccezione:", repr(e))

    # 3. Hawking + Hawking UV layer
    if hasattr(lmd, "append_hawking_layer_to_metrics"):
        try:
            metrics = lmd.append_hawking_layer_to_metrics(metrics)  # type: ignore[attr-defined]
        except Exception as e:
            print("[WARN] append_hawking_layer_to_metrics ha sollevato un'eccezione:", repr(e))

    # 3bis. Forziamo un regime Hawking UV di frontiera.
    # Usiamo valori compatibili con la logica del tag:
    #  - phase='trans_uv'
    #  - indice UV alto (>=10) => uv_frontier
    metrics["hawking_uv_phase"] = "trans_uv"
    metrics["hawking_uv_index"] = 15.0
    metrics["hawking_uv_energy"] = 3.0

    # 4. Planck layer
    if hasattr(lmd, "append_planck_layer_to_metrics"):
        try:
            metrics = lmd.append_planck_layer_to_metrics(metrics)  # type: ignore[attr-defined]
        except Exception as e:
            print("[WARN] append_planck_layer_to_metrics ha sollevato un'eccezione:", repr(e))

    # 5. Policy Bridge (decisione finale, incorporando il canale UV)
    if hasattr(lmd, "apply_policy_bridge_to_metrics"):
        try:
            metrics = lmd.apply_policy_bridge_to_metrics(metrics)  # type: ignore[attr-defined]
        except Exception as e:
            print("[WARN] apply_policy_bridge_to_metrics ha sollevato un'eccezione:", repr(e))

    if hasattr(lmd, "append_policy_bridge_to_metrics"):
        try:
            metrics = lmd.append_policy_bridge_to_metrics(metrics)  # type: ignore[attr-defined]
        except Exception as e:
            print("[WARN] append_policy_bridge_to_metrics ha sollevato un'eccezione:", repr(e))

    return metrics


def _fmt_pair(metrics, key):
    """Restituisce una stringa 'val (base=...)' per una coppia key/key_base se esiste."""
    base_key = f"{key}_base"
    val = metrics.get(key, None)
    base = metrics.get(base_key, None)
    if base is None:
        return f"{val!r}"
    if val == base:
        return f"{val!r} (base)"
    return f"{val!r} (base={base!r})"


def print_human_report(metrics):
    """Stampa un mini–report Loventre leggibile da umano per il case 2."""
    print("================================================================")
    print(" LOVENTRE DEMO CASE 2 – Scenario di frontiera Hawking UV")
    print("================================================================\n")

    print(">>> Identità del caso")
    print("  instance_id    :", metrics.get("instance_id"))
    print("  instance_label :", metrics.get("instance_label"))
    print()

    print(">>> Core Loventre + massa (valori correnti vs baseline)")
    for key in ["kappa_eff", "entropy_eff", "V0", "p_tunnel", "mass_mean", "chi", "risk_index"]:
        print(f"  {key:12s} = {_fmt_pair(metrics, key)}")
    print()

    print(">>> Layer fisici (se disponibili)")
    if "schwarzschild_regime" in metrics or "gamma_schw" in metrics:
        print("  Schwarzschild:")
        if "gamma_schw" in metrics:
            print("    gamma_schw         :", metrics.get("gamma_schw"))
        if "schwarzschild_regime" in metrics:
            print("    schwarzschild_regime:", metrics.get("schwarzschild_regime"))
    else:
        print("  Schwarzschild: nessuna metrica specifica trovata.")

    print()
    if "hawking_regime" in metrics or "hawking_uv_phase" in metrics:
        print("  Hawking:")
        if "hawking_regime" in metrics:
            print("    hawking_regime     :", metrics.get("hawking_regime"))
        if "hawking_uv_phase" in metrics:
            print("    hawking_uv_phase   :", metrics.get("hawking_uv_phase"))
        if "hawking_uv_index" in metrics:
            print("    hawking_uv_index   :", metrics.get("hawking_uv_index"))
        if "hawking_uv_energy" in metrics:
            print("    hawking_uv_energy  :", metrics.get("hawking_uv_energy"))
        if "hawking_uv_risk_comment" in metrics:
            print("    hawking_uv_risk_comment:")
            print("      ", metrics.get("hawking_uv_risk_comment"))
    else:
        print("  Hawking: nessuna metrica specifica trovata.")

    print()
    if "planck_regime" in metrics:
        print("  Planck:")
        print("    planck_regime      :", metrics.get("planck_regime"))
        if "planck_comment" in metrics:
            print("    planck_comment     :", metrics.get("planck_comment"))
    else:
        print("  Planck: nessuna metrica specifica trovata.")
    print()

    print(">>> Policy Bridge (decisione finale)")
    print("  policy_strategy      :", metrics.get("policy_strategy"))
    print("  policy_energy        :", metrics.get("policy_energy"))
    print("  policy_uv_tag        :", metrics.get("policy_uv_tag"))
    print("  policy_uv_note       :", metrics.get("policy_uv_note"))
    print("  policy_comment:")
    print("    ", metrics.get("policy_comment"))
    print()

    print(">>> Riepilogo rapido")
    risk = metrics.get("risk_index")
    uv_tag = metrics.get("policy_uv_tag")
    hawking_phase = metrics.get("hawking_uv_phase")
    print(f"  - Rischio finale          : {risk!r}")
    print(f"  - Regime Hawking UV       : phase={hawking_phase!r}, tag={uv_tag!r}")
    print(f"  - Strategia di policy     : {metrics.get('policy_strategy')!r}")
    print(f"  - Livello di energia      : {metrics.get('policy_energy')!r}")
    print()

    print("================================================================")
    print(" Fine LOVENTRE DEMO CASE 2")
    print("================================================================")


def main():
    lmd = import_meta_engine()
    core_metrics = build_frontier_core_metrics()
    metrics = run_pipeline_frontier(lmd, core_metrics)
    print_human_report(metrics)


if __name__ == "__main__":
    main()

