from pathlib import Path


NEW_DEF = """def _print_policy_bridge_section(metrics: dict) -> None:
    \"\"\"Stampa la sezione 'Loventre Policy Bridge' se i campi di policy sono presenti.

    Si aspetta che il meta-engine abbia popolato:
    - policy_strategy
    - policy_energy
    - policy_comment
    opzionalmente:
    - policy_bridge_warning (se il Policy Bridge non è disponibile o ha dato payload invalido).
    \"\"\"

    policy_strategy = metrics.get("policy_strategy")
    policy_energy = metrics.get("policy_energy")
    policy_comment = metrics.get("policy_comment")
    warning = metrics.get("policy_bridge_warning")

    # Se non abbiamo né strategia né warning, non stampiamo nulla.
    if not policy_strategy and not warning:
        return

    print()
    print("--- Loventre Policy Bridge ---")

    # Caso: warning presente e nessuna strategia valida.
    if warning and not policy_strategy:
        print(f"Nota: {warning}")
        return

    # Strategia principale
    print(f"Strategia Loventre: {policy_strategy}")

    # Policy energetica se disponibile
    if policy_energy is not None:
        print(f"Policy energetica: {policy_energy}")

    # Commento se disponibile
    if policy_comment:
        print(f"Commento: {policy_comment}")
"""


def patch_cli(path: Path) -> None:
    if not path.exists():
        print(f"⚠️  File non trovato: {path}")
        return

    text = path.read_text(encoding="utf-8")

    marker_start = "def _print_policy_bridge_section"
    marker_next = "def _print_planck_layer_section"

    start_idx = text.find(marker_start)
    if start_idx == -1:
        print("⚠️  Non trovata def _print_policy_bridge_section; nessuna patch applicata.")
        return

    next_idx = text.find(marker_next, start_idx)
    if next_idx == -1:
        print("⚠️  Non trovata def _print_planck_layer_section dopo _print_policy_bridge_section; nessuna patch applicata.")
        return

    new_text = text[:start_idx] + NEW_DEF + "\n\n" + text[next_idx:]
    path.write_text(new_text, encoding="utf-8")
    print("✅ Blocco _print_policy_bridge_section riscritto completamente.")
    print(f"✅ Patch applicata a {path}")


def main() -> None:
    cli_path = Path("loventre_meta_decision_cli.py")
    patch_cli(cli_path)


if __name__ == "__main__":
    main()

