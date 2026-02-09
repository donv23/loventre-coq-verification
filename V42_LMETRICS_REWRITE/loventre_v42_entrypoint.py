"""
loventre_v42_entrypoint.py
Loventre Engine — V42 LMetrics Rewrite
Gennaio 2026

Flusso:
 - carica ultimo V41
 - verifica minima sanità
 - lo promuove a policy_history_latest.json
"""

from V42_LMETRICS_REWRITE.loventre_v42_loader import load_latest_v41
from V42_LMETRICS_REWRITE.loventre_v42_rewriter import rewrite_policy_latest


def minimally_valid(lm):
    """
    Richiede almeno i campi base salvati da V41.
    """
    req = [
        "trend_label",
        "risk_label",
        "prognosis_label",
        "instability_flag",
        "recovery_flag",
    ]
    missing = [k for k in req if k not in lm]
    return (len(missing) == 0, missing)


def main():
    print("\n===== LOVENTRE ENGINE — V42 LMetrics REWRITE =====\n")

    path, lm = load_latest_v41()
    print(f"[V42] Caricato V41: {path}")
    print(f"[V42] Contenuto: {lm}")

    ok, missing = minimally_valid(lm)
    if not ok:
        print("[V42] ❌ VALIDAZIONE FALLITA")
        print(" Mancano:", missing)
        print(" Nessuna riscrittura eseguita.")
        return

    print("[V42] ✔ VALIDAZIONE OK — Promuovo LMetrics riparato...")
    latest, promoted = rewrite_policy_latest(path, lm)

    print("\n[V42] NUOVI FILE:")
    print(" Canonico:", latest)
    print(" Copia timestampata:", promoted)

    print("\n===== END V42 LMetrics REWRITE =====")


if __name__ == "__main__":
    main()

