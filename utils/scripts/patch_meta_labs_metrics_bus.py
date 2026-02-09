from pathlib import Path


def patch_meta_portfolio_lab(root: Path) -> None:
    target = root / "loventre_meta_portfolio_lab.py"
    if not target.exists():
        print("WARNING: loventre_meta_portfolio_lab.py not found, skipping.")
        return

    text = target.read_text(encoding="utf-8")
    changed = False

    # 1) Import del metrics bus
    if "from loventre_metrics_bus import ensure_loventre_keys" not in text:
        anchor = "from loventre_meta_decision_engine import _compute_risk_profile\n"
        if anchor in text:
            text = text.replace(
                anchor,
                anchor + "from loventre_metrics_bus import ensure_loventre_keys\n",
                1,
            )
            changed = True
        else:
            print("[meta_portfolio] WARNING: anchor for import not found; import not injected.")

    # 2) Normalizzazione metrics_by_seed con ensure_loventre_keys
    old_block = '''    for (param, factor) in SEEDS:
        m = meta_analyze_seed(param, factor, energy)
        m = enrich_metrics_with_time_dilation(
            m,
            gamma_cap=100.0,
            gamma_threshold_euclidean=2.0,
            gamma_threshold_hyperbolic=5.0,
        )
        metrics_by_seed[(param, factor)] = m
'''
    new_block = '''    for (param, factor) in SEEDS:
        m = meta_analyze_seed(param, factor, energy)
        m = enrich_metrics_with_time_dilation(
            m,
            gamma_cap=100.0,
            gamma_threshold_euclidean=2.0,
            gamma_threshold_hyperbolic=5.0,
        )
        # Allineamento al Loventre Metrics Bus (aggiunge region_label, np_like_label, ecc.)
        m = ensure_loventre_keys(m)
        metrics_by_seed[(param, factor)] = m
'''
    if "m = ensure_loventre_keys(m)" not in text:
        if old_block in text:
            text = text.replace(old_block, new_block, 1)
            changed = True
        else:
            print("[meta_portfolio] WARNING: metrics_by_seed block not found; ensure_loventre_keys not applied.")

    if changed:
        target.write_text(text, encoding="utf-8")
        print("loventre_meta_portfolio_lab.py updated for Loventre metrics bus.")
    else:
        print("loventre_meta_portfolio_lab.py already aligned with Loventre metrics bus.")


def patch_global_profile_lab(root: Path) -> None:
    target = root / "loventre_global_profile_lab.py"
    if not target.exists():
        print("WARNING: loventre_global_profile_lab.py not found, skipping.")
        return

    text = target.read_text(encoding="utf-8")
    changed = False

    # 1) Import del metrics bus
    if "from loventre_metrics_bus import ensure_loventre_keys" not in text:
        if "import math\n" in text:
            text = text.replace(
                "import math\n",
                "import math\nfrom loventre_metrics_bus import ensure_loventre_keys\n",
                1,
            )
            changed = True
        else:
            print("[global_profile] WARNING: 'import math' anchor not found; import not injected.")

    # 2) global_seed_profiles: normalizza f con ensure_loventre_keys
    old_block_seed = '''    for param in [1, 2, 3]:
        for factor in [1, 2, 3]:
            f = meta_analyze_seed(param, factor, energy)
            p = f["p_tunnel"]
            P_succ = success_probability(p, n_budget)
            decision = decision_from_probability(P_succ)
'''
    new_block_seed = '''    for param in [1, 2, 3]:
        for factor in [1, 2, 3]:
            f = meta_analyze_seed(param, factor, energy)
            # Allineamento al Loventre Metrics Bus (aggiunge region_label, np_like_label, ecc.)
            f = ensure_loventre_keys(f)
            p = f["p_tunnel"]
            P_succ = success_probability(p, n_budget)
            decision = decision_from_probability(P_succ)
'''
    if "f = ensure_loventre_keys(f)" not in text:
        if old_block_seed in text:
            text = text.replace(old_block_seed, new_block_seed, 1)
            changed = True
        else:
            print("[global_profile] WARNING: global_seed_profiles block not found; ensure_loventre_keys not applied there.")

    # 3) build_seed_grid_atlas: normalizza m con ensure_loventre_keys
    old_block_atlas = '''    # 1) metriche via meta_analyze_seed + time dilation
    metrics_by_seed: Dict[Tuple[int, int], Dict[str, Any]] = {}
    for (param, factor) in SEEDS:
        m = meta_analyze_seed(param, factor, energy)
        # garantiamo la presenza di gamma_dilation / time_regime
        m = enrich_metrics_with_time_dilation(
            m,
            gamma_cap=100.0,
            gamma_threshold_euclidean=2.0,
            gamma_threshold_hyperbolic=5.0,
        )
        metrics_by_seed[(param, factor)] = m
'''
    new_block_atlas = '''    # 1) metriche via meta_analyze_seed + time dilation
    metrics_by_seed: Dict[Tuple[int, int], Dict[str, Any]] = {}
    for (param, factor) in SEEDS:
        m = meta_analyze_seed(param, factor, energy)
        # garantiamo la presenza di gamma_dilation / time_regime
        m = enrich_metrics_with_time_dilation(
            m,
            gamma_cap=100.0,
            gamma_threshold_euclidean=2.0,
            gamma_threshold_hyperbolic=5.0,
        )
        # Allineamento al Loventre Metrics Bus
        m = ensure_loventre_keys(m)
        metrics_by_seed[(param, factor)] = m
'''
    if "m = ensure_loventre_keys(m)" not in text:
        if old_block_atlas in text:
            text = text.replace(old_block_atlas, new_block_atlas, 1)
            changed = True
        else:
            print("[global_profile] WARNING: build_seed_grid_atlas block not found; ensure_loventre_keys not applied there.")

    if changed:
        target.write_text(text, encoding="utf-8")
        print("loventre_global_profile_lab.py updated for Loventre metrics bus.")
    else:
        print("loventre_global_profile_lab.py already aligned with Loventre metrics bus.")


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    patch_meta_portfolio_lab(root)
    patch_global_profile_lab(root)


if __name__ == "__main__":
    main()

