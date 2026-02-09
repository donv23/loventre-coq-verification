from pathlib import Path
import ast
import sys


def main() -> None:
    path = Path("loventre_meta_decision_engine.py")
    try:
        code = path.read_text(encoding="utf-8")
    except FileNotFoundError:
        print("❌ File loventre_meta_decision_engine.py non trovato.")
        sys.exit(1)

    sentinel = "# === Loventre Policy Bridge canonical contract START ==="
    if sentinel in code:
        print("ℹ️  Blocco canonico Policy Bridge già presente; nessuna modifica.")
        return

    append_block = (
        "\n\n"
        "# === Loventre Policy Bridge canonical contract START ===\n"
        "def apply_policy_bridge_to_metrics(metrics: dict) -> dict:\n"
        "    \"\"\"Adapter tra metrics e Loventre Policy Bridge.\n"
        "\n"
        "    Usa loventre_local_decision(...) per derivare una decisione locale\n"
        "    a partire da risk_index, K_globale/Schwarzschild e layer relativistici.\n"
        "    I risultati vengono esposti come chiavi 'policy_*' in metrics.\n"
        "    In caso di errore o assenza del modulo, ritorna i metrics invariati.\n"
        "    \"\"\"\n"
        "    try:\n"
        "        from loventre_policy_bridge_lab import loventre_local_decision\n"
        "    except Exception:\n"
        "        return metrics\n"
        "\n"
        "    risk_index = metrics.get(\"risk_index\")\n"
        "    k_global = metrics.get(\"schwarzschild_K_global\")\n"
        "    if k_global is None:\n"
        "        k_global = metrics.get(\"K_globale\")\n"
        "    chi = metrics.get(\"compactness\")\n"
        "    if chi is None:\n"
        "        chi = metrics.get(\"schwarzschild_compactness\")\n"
        "    gamma_schw = metrics.get(\"gamma_schwarzschild\")\n"
        "\n"
        "    try:\n"
        "        decision = loventre_local_decision(\n"
        "            risk_index=risk_index,\n"
        "            k_global=k_global,\n"
        "            chi=chi,\n"
        "            gamma_schw=gamma_schw,\n"
        "        )\n"
        "    except Exception:\n"
        "        return metrics\n"
        "\n"
        "    strategy = getattr(decision, \"strategy_decision\", None)\n"
        "    energy = getattr(decision, \"energy_policy\", None)\n"
        "    comment = getattr(decision, \"comment\", None)\n"
        "\n"
        "    if strategy is not None:\n"
        "        metrics[\"policy_strategy\"] = strategy\n"
        "    if energy is not None:\n"
        "        metrics[\"policy_energy\"] = energy\n"
        "    if comment is not None:\n"
        "        metrics[\"policy_comment\"] = comment\n"
        "\n"
        "    return metrics\n"
        "\n"
        "def append_policy_bridge_to_metrics(metrics: dict) -> dict:\n"
        "    \"\"\"Appende un blocco testuale di Loventre Policy Bridge a meta_explanation.\n"
        "\n"
        "    Non modifica altri campi numerici; è puro layer di spiegazione.\n"
        "    Se i campi 'policy_*' non sono presenti, non fa nulla.\n"
        "    \"\"\"\n"
        "    strategy = metrics.get(\"policy_strategy\")\n"
        "    energy = metrics.get(\"policy_energy\")\n"
        "    comment = metrics.get(\"policy_comment\")\n"
        "\n"
        "    if strategy is None and energy is None and comment is None:\n"
        "        return metrics\n"
        "\n"
        "    lines = []\n"
        "    lines.append(\"- Loventre Policy Bridge:\")\n"
        "    if strategy is not None:\n"
        "        lines.append(\"  Strategia Loventre: {0}\".format(strategy))\n"
        "    if energy is not None:\n"
        "        lines.append(\"  Policy energetica: {0}\".format(energy))\n"
        "    if comment is not None:\n"
        "        lines.append(\"  Nota: {0}\".format(comment))\n"
        "\n"
        "    block = \"\\n\".join(lines)\n"
        "\n"
        "    base_expl = metrics.get(\"meta_explanation\", \"\").rstrip()\n"
        "    if base_expl:\n"
        "        new_expl = base_expl + \"\\n\\n\" + block\n"
        "    else:\n"
        "        new_expl = block\n"
        "\n"
        "    metrics[\"meta_explanation\"] = new_expl\n"
        "    return metrics\n"
        "# === Loventre Policy Bridge canonical contract END ===\n"
    )

    patched = code + append_block

    try:
        ast.parse(patched)
    except SyntaxError as e:
        print("❌ Errore di sintassi dopo la patch: {0}".format(e))
        sys.exit(1)

    path.write_text(patched, encoding="utf-8")
    print("✅ Blocco canonico Policy Bridge aggiunto in coda al file.")
    print("✅ Sintassi verificata con ast.parse.")


if __name__ == "__main__":
    main()

