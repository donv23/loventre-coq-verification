"""
loventre_v39_entrypoint.py
Loventre Engine — V39 COQ Probe Entrypoint
Gennaio 2026

Step:
 1) Legge ultimo JSON V38
 2) Ispeziona campi chiave LMetrics
 3) Stampa un report leggibile per Coq developer
"""

from V38_LMETRICS_COQ_IMPORT.loventre_v38_coq_json_reader import load_latest_lmetrics
from V39_JSON_TO_COQ_PROBE.loventre_v39_probe import probe_lmetrics_dict


def main():
    print("\n===== LOVENTRE ENGINE — V39 JSON→COQ PROBE =====\n")

    try:
        src, lm = load_latest_lmetrics()
        print(f"[V39] Caricato LMetrics V38 da: {src}")
    except Exception as e:
        print(f"[V39 ERROR] {e}")
        return

    print("\n[V39] Analisi dei campi chiave...")
    report = probe_lmetrics_dict(lm)

    print("\n--- V39 PROBE REPORT ---")
    for k, v in report.items():
        print(f"{k}: {v}")

    print("\n===== END V39 JSON→COQ PROBE =====")


if __name__ == "__main__":
    main()

