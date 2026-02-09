from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "loventre_meta_portfolio_lab.py"

OLD_PRINT_BLOCK = '''    for r in records:
        short_diff = r["difficulty_label"].split("(")[0].strip()
        print(
            f"{r['param']:5d} {r['factor']:6d} "
            f"{r['region']:9} "
            f"{str(r['P_like']):6} {str(r['NP_like']):7} "
            f"{r['pattern_c']:30} "
            f"{r['risk_index']:5.2f} {r['risk_label']:11s} "
            f"{r['loventre_score']:6.3f} "
            f"{r['strategy_score']:6.3f} "
            f"{r['V0']:7.4f} "
            f"{r['p_tunnel']:11.3e} "
            f"{r['p_success']:11.3e} "
            f"{r['difficulty_index']:8.3f} "
            f"{short_diff:35} "
            f"{r['geod_chaos_index']:7.3f} "
            f"{r['geod_regime']:12s} "
            f"{r['decision_label']}"
        )
'''

NEW_PRINT_BLOCK = '''    for r in records:
        short_diff = r["difficulty_label"].split("(")[0].strip()
        print(
            f"{r['param']:5d} {r['factor']:6d} "
            f"{r['region']:9} "
            f"{str(r['P_like']):6} {str(r['NP_like']):7} "
            f"{r['pattern_c']:30} "
            f"{r['risk_index']:5.2f} {r['risk_label']:11s} "
            f"{r['loventre_score']:6.3f} "
            f"{r['strategy_score']:6.3f} "
            f"{r.get('global_decision', 'N/A'):6s} "
            f"{r.get('global_color', 'N/A'):5s} "
            f"{r.get('global_score', 0.0):6.3f} "
            f"{r['V0']:7.4f} "
            f"{r['p_tunnel']:11.3e} "
            f"{r['p_success']:11.3e} "
            f"{r['difficulty_index']:8.3f} "
            f"{short_diff:35} "
            f"{r['geod_chaos_index']:7.3f} "
            f"{r['geod_regime']:12s} "
            f"{r['decision_label']}"
        )
'''


def main() -> None:
    if not TARGET.exists():
        raise SystemExit(f"File non trovato: {TARGET}")

    text = TARGET.read_text(encoding="utf-8")

    # Patch idempotente: sostituiamo SOLO se troviamo ancora il blocco originale
    if OLD_PRINT_BLOCK not in text:
        print("Blocco di print originale non trovato: probabilmente già patchato.")
        return

    text_new = text.replace(OLD_PRINT_BLOCK, NEW_PRINT_BLOCK)
    TARGET.write_text(text_new, encoding="utf-8")
    print("loventre_meta_portfolio_lab.py: print dei seed aggiornata con global_decision/global_color/global_score.")


if __name__ == "__main__":
    main()

