from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "loventre_meta_portfolio_lab.py"


def patch_imports(text: str) -> str:
    """
    Aggiunge loventre_global_decision all'import da loventre_meta_decision_engine
    se non è già presente.
    """
    if "loventre_global_decision" in text:
        return text

    old = "from loventre_meta_decision_engine import _compute_risk_profile\n"
    new = (
        "from loventre_meta_decision_engine import _compute_risk_profile, "
        "loventre_global_decision\n"
    )
    if old in text:
        return text.replace(old, new)
    return text


def patch_header(text: str) -> str:
    """
    Inserisce colonne G_dec / G_col / G_scr nell'header della tabella seed.
    """
    if "G_dec" in text and "G_col" in text and "G_scr" in text:
        return text

    old_header = (
        '    header = (\n'
        '        "param factor region      P_like NP_like "\n'
        '        "pattern_c                     "\n'
        '        "risk   risk_label score  strat   V0       p_tunnel(E)   P_success   diff_idx  diff_label                           geod_ch  geod_reg      decision"\n'
        '    )\n'
    )

    new_header = (
        '    header = (\n'
        '        "param factor region      P_like NP_like "\n'
        '        "pattern_c                     "\n'
        '        "risk   risk_label score  strat   G_dec  G_col  G_scr   V0       p_tunnel(E)   P_success   diff_idx  diff_label                           geod_ch  geod_reg      decision"\n'
        '    )\n'
    )

    if old_header in text:
        return text.replace(old_header, new_header)
    return text


def patch_global_decision_call(text: str) -> str:
    """
    Inserisce la chiamata a loventre_global_decision dentro build_seed_metrics_map.
    """
    if "loventre_global_decision(m, family=\"seed_grid\")" in text:
        return text

    marker = (
        "        g = geod_data[(param, factor)]\n"
        "\n"
        "        record = {\n"
    )

    insert = (
        "        try:\n"
        "            g_decision = loventre_global_decision(m, family=\"seed_grid\")\n"
        "            global_decision = g_decision.get(\"global_decision\", \"N/A\")\n"
        "            global_color = g_decision.get(\"global_color\", \"N/A\")\n"
        "            global_score = float(g_decision.get(\"global_score\", 0.0) or 0.0)\n"
        "        except Exception:\n"
        "            global_decision = \"N/A\"\n"
        "            global_color = \"N/A\"\n"
        "            global_score = 0.0\n"
        "\n"
        "        g = geod_data[(param, factor)]\n"
        "\n"
        "        record = {\n"
    )

    if marker in text:
        return text.replace(marker, insert)
    return text


def patch_record_fields(text: str) -> str:
    """
    Aggiunge i campi global_decision / global_color / global_score nel record seed.
    """
    if "global_decision" in text and "global_color" in text and "global_score" in text:
        return text

    old_block = (
        '        record = {\n'
        '            "param": param,\n'
        '            "factor": factor,\n'
        '            "region": m.get("region", "unknown"),\n'
        '            "P_like": bool(m.get("P_like", False)),\n'
        '            "NP_like": bool(m.get("NP_like", False)),\n'
        '            "pattern_c": m.get("pattern_c", ""),\n'
        '            "loventre_score": float(m.get("loventre_score", 0.0)),\n'
        '            "difficulty_label": m.get("difficulty_label", ""),\n'
    )

    new_block = (
        '        record = {\n'
        '            "param": param,\n'
        '            "factor": factor,\n'
        '            "region": m.get("region", "unknown"),\n'
        '            "P_like": bool(m.get("P_like", False)),\n'
        '            "NP_like": bool(m.get("NP_like", False)),\n'
        '            "pattern_c": m.get("pattern_c", ""),\n'
        '            "loventre_score": float(m.get("loventre_score", 0.0)),\n'
        '            "difficulty_label": m.get("difficulty_label", ""),\n'
        '            "global_decision": global_decision,\n'
        '            "global_color": global_color,\n'
        '            "global_score": global_score,\n'
    )

    if old_block in text:
        return text.replace(old_block, new_block)
    return text


def patch_print_line(text: str) -> str:
    """
    Inserisce la stampa di global_decision / global_color / global_score nella riga del portafoglio.
    """
    if "global_decision" in text and "global_color" in text and "global_score" in text:
        return text

    old_print = (
        '        print(\n'
        '            f"{r[\'param\']:5d} {r[\'factor\']:6d} "\n'
        '            f"{r[\'region\']:9} "\n'
        '            f"{str(r[\'P_like\']):6} {str(r[\'NP_like\']):7} "\n'
        '            f"{r[\'pattern_c\']:30} "\n'
        '            f"{r[\'risk_index\']:5.2f} {r[\'risk_label\']:11s} "\n'
        '            f"{r[\'loventre_score\']:6.3f} "\n'
        '            f"{r[\'strategy_score\']:6.3f} "\n'
        '            f"{r[\'V0\']:7.4f} "\n'
        '            f"{r[\'p_tunnel\']:11.3e} "\n'
        '            f"{r[\'p_success\']:11.3e} "\n'
        '            f"{r[\'difficulty_index\']:8.3f} "\n'
        '            f"{short_diff:35} "\n'
        '            f"{r[\'geod_chaos_index\']:7.3f} "\n'
        '            f"{r[\'geod_regime\']:12s} "\n'
        '            f"{r[\'decision_label\']}"\n'
        '        )\n'
    )

    new_print = (
        '        print(\n'
        '            f"{r[\'param\']:5d} {r[\'factor\']:6d} "\n'
        '            f"{r[\'region\']:9} "\n'
        '            f"{str(r[\'P_like\']):6} {str(r[\'NP_like\']):7} "\n'
        '            f"{r[\'pattern_c\']:30} "\n'
        '            f"{r[\'risk_index\']:5.2f} {r[\'risk_label\']:11s} "\n'
        '            f"{r[\'loventre_score\']:6.3f} "\n'
        '            f"{r[\'strategy_score\']:6.3f} "\n'
        '            f"{r.get(\'global_decision\', \'N/A\'):6s} "\n'
        '            f"{r.get(\'global_color\', \'N/A\'):5s} "\n'
        '            f"{r.get(\'global_score\', 0.0):6.3f} "\n'
        '            f"{r[\'V0\']:7.4f} "\n'
        '            f"{r[\'p_tunnel\']:11.3e} "\n'
        '            f"{r[\'p_success\']:11.3e} "\n'
        '            f"{r[\'difficulty_index\']:8.3f} "\n'
        '            f"{short_diff:35} "\n'
        '            f"{r[\'geod_chaos_index\']:7.3f} "\n'
        '            f"{r[\'geod_regime\']:12s} "\n'
        '            f"{r[\'decision_label\']}"\n'
        '        )\n'
    )

    if old_print in text:
        return text.replace(old_print, new_print)
    return text


def main() -> None:
    if not TARGET.exists():
        raise SystemExit(f"File non trovato: {TARGET}")

    text = TARGET.read_text(encoding="utf-8")

    original = text
    text = patch_imports(text)
    text = patch_header(text)
    text = patch_global_decision_call(text)
    text = patch_record_fields(text)
    text = patch_print_line(text)

    if text != original:
        TARGET.write_text(text, encoding="utf-8")
        print("loventre_meta_portfolio_lab.py aggiornato con global_decision.")
    else:
        print("Nessuna modifica necessaria (già patchato?).")


if __name__ == "__main__":
    main()

