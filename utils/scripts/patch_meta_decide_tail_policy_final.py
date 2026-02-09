from pathlib import Path

OLD_TAIL = """    metrics = append_planck_layer_to_metrics(metrics)
    metrics = apply_policy_bridge_to_metrics(metrics)
    append_policy_bridge_to_metrics(metrics)
    return metrics
"""

NEW_TAIL = """    # Layer Planck–Loventre (cutoff UV)
    metrics = append_planck_layer_to_metrics(metrics)

    # Loventre Policy Bridge: unico punto canonico per strategia/energia
    metrics = append_policy_bridge_to_metrics(metrics)

    return metrics
"""


def patch_file(path: Path) -> None:
    if not path.exists():
        print(f"⚠️  File non trovato: {path}")
        return

    text = path.read_text(encoding="utf-8")

    if OLD_TAIL not in text:
        print("⚠️  Pattern tail meta_decide_instance_with_mass non trovato; nessuna patch applicata.")
        return

    new_text = text.replace(OLD_TAIL, NEW_TAIL)
    path.write_text(new_text, encoding="utf-8")
    print("✅ Tail di meta_decide_instance_with_mass riscritto (Planck → Policy → return).")
    print(f"✅ Patch applicata a {path}")


def main() -> None:
    engine_path = Path("loventre_meta_decision_engine.py")
    patch_file(engine_path)


if __name__ == "__main__":
    main()

