from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "loventre_meta_portfolio_lab.py"


def main() -> None:
    if not TARGET.exists():
        raise SystemExit(f"File non trovato: {TARGET}")

    text = TARGET.read_text(encoding="utf-8")

    # Se abbiamo già inserito il blocco con m_seed, non facciamo nulla
    if 'loventre_global_decision(m_seed, family="seed_grid")' in text:
        print("Global decision già collegato ai seed, nessuna modifica.")
        return

    old = "    return data_map\n"
    new = '''    # Aggancio globale Loventre (global_decision/global_color/global_score)
    try:
        from loventre_meta_decision_engine import loventre_global_decision
        for key, rec in data_map.items():
            m_seed = metrics_by_seed.get(key)
            if m_seed is None:
                continue
            try:
                gdec = loventre_global_decision(m_seed, family="seed_grid")
            except Exception:
                continue
            if isinstance(gdec, dict):
                rec["global_decision"] = gdec.get("global_decision")
                rec["global_color"] = gdec.get("global_color")
                rec["global_score"] = gdec.get("global_score")
    except Exception:
        # Se qualcosa va storto, lasciamo i record intatti (N/A)
        pass

    return data_map
'''

    if old not in text:
        raise SystemExit("Pattern 'return data_map' non trovato o già modificato.")

    text_new = text.replace(old, new)
    TARGET.write_text(text_new, encoding="utf-8")
    print("loventre_meta_portfolio_lab.py: seed arricchiti con global_decision/global_color/global_score.")


if __name__ == "__main__":
    main()

