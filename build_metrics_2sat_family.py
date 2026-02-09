import json
from pathlib import Path
from loventre_sat_2sat_family import summarize_2sat_instance


# ============================================================
# Loventre Engine – 2-SAT Metrics Builder (Dicembre 2025)
# ============================================================
# Genera i due file:
#   metrics_2SAT_easy_demo.json
#   metrics_2SAT_crit_demo.json
# a partire dalla geometria Loventre calcolata
# in loventre_sat_2sat_family.py
# ============================================================

def make_metrics_dict(name: str, energy: float, n_budget: int) -> dict:
    summary = summarize_2sat_instance(name, energy, n_budget)

    # Struttura coerente con metrics_seed11_cli_demo.json
    metrics = {
        "chi_compactness": 0.2,  # default simbolico
        "horizon_flag": False,
        "loventre_global": {
            "global_decision": summary["target_global_decision"].replace("GD_", "").upper(),
            "global_color": summary["target_global_color"].replace("GC_", "").upper(),
            "global_score": round(summary["P_success"], 2),
        },
        "meta_label": summary["target_meta_label"],
        "p_tunnel": round(summary["p_tunnel"], 3),
        "risk_class": summary["target_risk_class"].replace("risk_", "").upper(),
        "risk_index": 2.0 if "easy" in name else 3.0,
        "time_regime": "time_euclidean",
        "kappa_eff": round(summary["kappa_eff"], 3),
        "entropy_eff": round(summary["entropy_eff"], 3),
        "V0": round(summary["V0"], 3),
        "expected_attempts": round(summary["expected_N"], 2),
        "P_success": round(summary["P_success"], 3),
        "regime_hint": summary["regime_hint"],
    }

    return metrics


def save_metrics_to_json(metrics: dict, filename: str) -> None:
    path = Path(filename)
    with path.open("w", encoding="utf-8") as f:
        json.dump(metrics, f, indent=2, ensure_ascii=False)
    print(f"[OK] Salvato {filename}")


def main() -> None:
    print("==============================================================")
    print("=== LOVENTRE ENGINE – COSTRUZIONE METRICS 2-SAT (v3)       ===")
    print("==============================================================")
    print()

    energy = 0.5
    n_budget = 10000

    easy_metrics = make_metrics_dict("2SAT_easy_demo", energy, n_budget)
    crit_metrics = make_metrics_dict("2SAT_crit_demo", energy, n_budget)

    save_metrics_to_json(easy_metrics, "metrics_2SAT_easy_demo.json")
    save_metrics_to_json(crit_metrics, "metrics_2SAT_crit_demo.json")

    print()
    print(">>> Riepilogo sintetico:")
    for name, m in [("2SAT_easy", easy_metrics), ("2SAT_crit", crit_metrics)]:
        print(f"\n--- {name} ---")
        print(f"  kappa_eff   : {m['kappa_eff']}")
        print(f"  entropy_eff : {m['entropy_eff']}")
        print(f"  V0          : {m['V0']}")
        print(f"  p_tunnel    : {m['p_tunnel']}")
        print(f"  P_success   : {m['P_success']}")
        print(f"  decision    : {m['loventre_global']['global_decision']}")
        print(f"  color       : {m['loventre_global']['global_color']}")
        print(f"  meta_label  : {m['meta_label']}")
        print(f"  risk_class  : {m['risk_class']}")
        print(f"  horizon_flag: {m['horizon_flag']}")
    print()
    print("[COMPLETATO] Costruiti entrambi i metrics JSON 2-SAT.")


if __name__ == "__main__":
    main()

