from pathlib import Path


MODULE_IMPORT = "from loventre_metrics_bus import ensure_loventre_keys\n\n"


METRICS_BLOCK_OLD = '''    metrics = {
        "V0": V0_est,
        "a_min": a_min,
        "E": E,
        "p_tunnel": p,
        "expected_attempts": N_mean,
        "U_values": U_values,
        "kappa_values": kappa_values,
        "classification": classification,
        "barrier_occupancy": barrier_occupancy,
    }

    return metrics
'''


METRICS_BLOCK_NEW = '''    metrics = {
        "V0": V0_est,
        "a_min": a_min,
        "E": E,
        "p_tunnel": p,
        "expected_attempts": N_mean,
        "U_values": U_values,
        "kappa_values": kappa_values,
        "classification": classification,
        "barrier_occupancy": barrier_occupancy,
    }

    # --- Loventre metrics bus normalisation ---
    metrics = ensure_loventre_keys(metrics)

    # Spatial classification alias in the Loventre vocabulary
    metrics["region_label"] = metrics.get("classification")

    # Toy NP-like label:
    #   - critical   -> NP_like_critical
    #   - otherwise  -> P_like
    region = metrics.get("region_label")
    if region == "critical":
        metrics.setdefault("np_like_label", "NP_like_critical")
    else:
        metrics.setdefault("np_like_label", "P_like")

    return metrics
'''


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    target = root / "loventre_instance_analysis.py"

    if not target.exists():
        print("ERROR: loventre_instance_analysis.py not found.")
        return

    text = target.read_text(encoding="utf-8")
    changed = False

    # 1) Aggiungi l'import del metrics bus dopo 'import math'
    if "from loventre_metrics_bus import ensure_loventre_keys" not in text:
        if "import math\n\n" in text:
            text = text.replace("import math\n\n", "import math\n\n" + MODULE_IMPORT, 1)
            changed = True
        else:
            print("WARNING: pattern 'import math' not found in expected form; import not injected.")

    # 2) Sostituisci il blocco di costruzione di metrics con la versione bus-aware
    if "metrics = ensure_loventre_keys(metrics)" not in text:
        if METRICS_BLOCK_OLD in text:
            text = text.replace(METRICS_BLOCK_OLD, METRICS_BLOCK_NEW, 1)
            changed = True
        else:
            print("WARNING: metrics block pattern not found; metrics normalisation not applied.")

    if changed:
        target.write_text(text, encoding="utf-8")
        print("loventre_instance_analysis.py updated for Loventre metrics bus.")
    else:
        print("loventre_instance_analysis.py already aligned with Loventre metrics bus.")


if __name__ == "__main__":
    main()

