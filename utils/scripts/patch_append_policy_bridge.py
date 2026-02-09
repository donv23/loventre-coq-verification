from pathlib import Path
import re

APPEND_POLICY_DEF = """\
def append_policy_bridge_to_metrics(metrics, overwrite=False):
    \"\"\"Attach Loventre Policy Bridge decision to metrics.

    Thin glue around loventre_policy_bridge_lab.loventre_local_decision.

    Design goals:
    - keep the engine stable even if the Policy Bridge is missing or misconfigured;
    - be robust to different decision payload formats (dataclass-like, dict, tuple);
    - enrich meta_explanation with a single compact Policy line.
    \"\"\"

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
    # We only rely on the core signature:
    #   loventre_local_decision(risk_index, k_global, chi, gamma_schw)
    decision = loventre_local_decision(risk_index, k_global, chi, gamma_schw)

    strategy = None
    energy = None
    comment = None

    # Decision can be:
    # - a dataclass-like object with .strategy/.energy/.comment
    # - a dict with keys "strategy"/"energy"/"comment"
    # - a tuple/list (strategy, energy, comment, ...)
    if hasattr(decision, "strategy") or hasattr(decision, "energy") or hasattr(decision, "comment"):
        strategy = getattr(decision, "strategy", None)
        energy = getattr(decision, "energy", None)
        comment = getattr(decision, "comment", None)

    if isinstance(decision, dict):
        strategy = decision.get("strategy", strategy)
        energy = decision.get("energy", energy)
        comment = decision.get("comment", comment)
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

    # meta_explanation enrichment (kept extremely compact)
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
"""


def patch_meta_decision_engine(path: Path) -> None:
    if not path.exists():
        print(f"⚠️  File non trovato: {path}")
        return

    original_text = path.read_text(encoding="utf-8")
    text = original_text
    changed = False

    # 1. Insert append_policy_bridge_to_metrics definition if missing.
    if "def append_policy_bridge_to_metrics" not in text:
        anchor = "def meta_decide_instance_with_mass"
        if anchor in text:
            text = text.replace(
                anchor,
                APPEND_POLICY_DEF + "\n\n" + anchor,
                1,
            )
            print("✅ Inserita def append_policy_bridge_to_metrics prima di meta_decide_instance_with_mass")
        else:
            # Fallback: append at end of file.
            text = text.rstrip() + "\n\n" + APPEND_POLICY_DEF + "\n"
            print("⚠️  Anchor meta_decide_instance_with_mass non trovata; def append_policy_bridge_to_metrics aggiunta in coda al file")
        changed = True
    else:
        print("ℹ️  def append_policy_bridge_to_metrics esiste già; nessuna reiniezione effettuata")

    # 2. Hook: call append_policy_bridge_to_metrics(metrics) after append_planck_layer_to_metrics(metrics)
    if "append_policy_bridge_to_metrics(metrics)" in text:
        print("ℹ️  Hook append_policy_bridge_to_metrics(metrics) già presente; nessuna modifica al blocco di chiamata")
    else:
        pattern = r"(\\n[ \\t]*)append_planck_layer_to_metrics\\(metrics\\)"
        replacement = (
            r"\\1append_planck_layer_to_metrics(metrics)\\n"
            r"\\1append_policy_bridge_to_metrics(metrics)"
        )
        new_text, n_sub = re.subn(pattern, replacement, text, count=1)
        if n_sub == 1:
            text = new_text
            changed = True
            print("✅ Agganciata append_policy_bridge_to_metrics(metrics) dopo append_planck_layer_to_metrics(metrics)")
        else:
            print("⚠️  Pattern append_planck_layer_to_metrics(metrics) non trovato; nessun hook aggiunto (verificare manualmente dove chiamare append_policy_bridge_to_metrics)")

    if changed:
        path.write_text(text, encoding="utf-8")
        print(f"✅ Patch applicata a {path}")
    else:
        print(f"ℹ️  Nessuna modifica necessaria per {path}")


def main() -> None:
    engine_path = Path("loventre_meta_decision_engine.py")
    patch_meta_decision_engine(engine_path)


if __name__ == "__main__":
    main()

