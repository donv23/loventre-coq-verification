from pathlib import Path
import re


NEW_DEF = '''def append_policy_bridge_to_metrics(metrics, overwrite=False):
    """Attach Loventre Policy Bridge decision to metrics (thin glue).

    This version is aligned with LoventrePolicyDecision in loventre_policy_bridge_lab,
    which exposes: strategy_decision, energy_policy, comment.
    """

    try:
        from loventre_policy_bridge_lab import loventre_local_decision
    except Exception as e:
        # Engine must remain stable even if Policy Bridge is not available.
        metrics.setdefault(
            "policy_bridge_warning",
            f"Loventre Policy Bridge not available: {e}",
        )
        return metrics

    risk_index = metrics.get("risk_index")
    if risk_index is None:
        metrics.setdefault(
            "policy_bridge_warning",
            "Loventre Policy Bridge: missing risk_index; policy not applied.",
        )
        return metrics

    # Support both English and Italian naming for K_global (if present).
    k_global = metrics.get("K_global") or metrics.get("K_globale")

    # Schwarzschild layer: we prefer the explicitly named keys if present.
    chi = metrics.get("schwarzschild_chi") or metrics.get("chi")
    gamma_schw = metrics.get("schwarzschild_gamma") or metrics.get("gamma_schw")

    # Call the local policy decision engine.
    decision = loventre_local_decision(risk_index, k_global, chi, gamma_schw)

    strategy = None
    energy = None
    comment = None

    # 1) Dataclass-style object (LoventrePolicyDecision:
    #    strategy_decision, energy_policy, comment)
    if hasattr(decision, "strategy_decision") or hasattr(decision, "energy_policy") or hasattr(decision, "comment"):
        strategy = getattr(decision, "strategy_decision", strategy)
        energy = getattr(decision, "energy_policy", energy)
        comment = getattr(decision, "comment", comment)

    # 2) Dict fallback
    if isinstance(decision, dict):
        strategy = decision.get("strategy_decision", decision.get("strategy", strategy))
        energy = decision.get("energy_policy", decision.get("energy", energy))
        comment = decision.get("comment", comment)

    # 3) Tuple/list fallback
    elif isinstance(decision, (tuple, list)):
        if len(decision) >= 1 and strategy is None:
            strategy = decision[0]
        if len(decision) >= 2 and energy is None:
            energy = decision[1]
        if len(decision) >= 3 and comment is None:
            comment = decision[2]

    if strategy is None:
        metrics.setdefault(
            "policy_bridge_warning",
            "Loventre Policy Bridge: invalid decision payload; policy not applied.",
        )
        return metrics

    if overwrite:
        metrics["policy_strategy"] = strategy
        metrics["policy_energy"] = energy
        metrics["policy_comment"] = comment
    else:
        metrics.setdefault("policy_strategy", strategy)
        metrics.setdefault("policy_energy", energy)
        metrics.setdefault("policy_comment", comment)

    # meta_explanation enrichment (kept compact)
    meta_expl = metrics.get("meta_explanation") or ""
    regime = metrics.get("planck_regime") or "unknown_planck_regime"
    line = (
        f"[Policy Bridge] strategia={strategy}; "
        f"energia={energy}; regime={regime}; commento={comment}"
    )

    if meta_expl:
        metrics["meta_explanation"] = meta_expl.rstrip() + "\\n" + line
    else:
        metrics["meta_explanation"] = line

    return metrics
'''


def patch_append_policy_def(path: Path) -> None:
    if not path.exists():
        print(f"⚠️  File non trovato: {path}")
        return

    text = path.read_text(encoding="utf-8")

    pattern = r"def append_policy_bridge_to_metrics\(metrics, overwrite=False\):\n(?:    .*\n)*"

    if "def append_policy_bridge_to_metrics" not in text:
        print("⚠️  Nessuna definizione di append_policy_bridge_to_metrics trovata; nessuna patch applicata.")
        return

    new_text, n_sub = re.subn(pattern, NEW_DEF + "\n", text, count=1)
    if n_sub == 0:
        print("⚠️  La regex non è riuscita a sostituire la definizione; nessuna patch applicata.")
        return

    path.write_text(new_text, encoding="utf-8")
    print("✅ Definizione di append_policy_bridge_to_metrics aggiornata.")
    print(f"✅ Patch applicata a {path}")


def main() -> None:
    engine_path = Path("loventre_meta_decision_engine.py")
    patch_append_policy_def(engine_path)


if __name__ == "__main__":
    main()

