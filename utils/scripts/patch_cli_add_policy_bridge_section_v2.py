from pathlib import Path
import ast


def main() -> None:
    path = Path("loventre_meta_decision_cli.py")
    code = path.read_text(encoding="utf-8")

    # Se la definizione esiste già, non tocchiamo nulla.
    if "def _print_policy_bridge_section(" in code:
        print("ℹ️  def _print_policy_bridge_section è già presente; nessuna modifica applicata.")
        return

    marker = "def _print_planck_layer_section("
    idx = code.find(marker)
    if idx == -1:
        print("⚠️  Non trovato 'def _print_planck_layer_section('; impossibile agganciare la sezione Policy Bridge.")
        return

    policy_block = """
def _print_policy_bridge_section(metrics: dict) -> None:
    \"\"\"Stampa la sezione 'Loventre Policy Bridge', se i campi policy sono presenti.\"\"\"
    strategy = metrics.get("policy_strategy")
    energy = metrics.get("policy_energy")
    comment = metrics.get("policy_comment")

    # Se non ci sono dati di policy, non stampiamo nulla
    if strategy is None and energy is None and comment is None:
        return

    print()
    print("--- Loventre Policy Bridge ---")
    if strategy is not None:
        print("Strategia Loventre: {}".format(strategy))
    if energy is not None:
        print("Policy energetica: {}".format(energy))
    if comment is not None:
        print("Commento: {}".format(comment))


"""

    new_code = code[:idx] + policy_block + code[idx:]

    # Verifica sintassi prima di scrivere sul file
    try:
        ast.parse(new_code)
    except SyntaxError as e:
        print("❌ Errore di sintassi dopo l'iniezione della sezione Policy Bridge:", e)
        return

    path.write_text(new_code, encoding="utf-8")
    print("✅ Sezione _print_policy_bridge_section inserita prima di _print_planck_layer_section.")
    print("✅ Sintassi di loventre_meta_decision_cli.py verificata con ast.parse.")


if __name__ == "__main__":
    main()

