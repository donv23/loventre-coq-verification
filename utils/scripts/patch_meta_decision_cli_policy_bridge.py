from pathlib import Path
import re


def patch_meta_decision_cli(path: Path) -> None:
    if not path.exists():
        print(f"⚠️  File non trovato: {path}")
        return

    text = path.read_text(encoding="utf-8")
    changed = False

    # Se esiste già una sezione Loventre Policy Bridge, non facciamo nulla.
    if "Loventre Policy Bridge" in text:
        print("ℹ️  Sezione 'Loventre Policy Bridge' già presente; nessuna modifica.")
        return

    # Cerchiamo la riga che stampa lo Strato Planck–Loventre
    pattern = r'^(?P<indent>[ \t]*)print\((?P<content>.*Strato Planck–Loventre.*)\)\s*$'
    match = re.search(pattern, text, flags=re.MULTILINE)

    if not match:
        print("⚠️  Non trovata la riga di stampa per 'Strato Planck–Loventre'; nessuna patch applicata.")
        return

    indent = match.group("indent")
    insert_pos = match.end()

    policy_block = (
        "\n"
        f"{indent}# --- Loventre Policy Bridge (se disponibile) ---\n"
        f"{indent}try:\n"
        f"{indent}    policy_strategy = metrics.get('policy_strategy')\n"
        f"{indent}    policy_energy = metrics.get('policy_energy')\n"
        f"{indent}    policy_comment = metrics.get('policy_comment')\n"
        f"{indent}except Exception:\n"
        f"{indent}    policy_strategy = None\n"
        f"{indent}    policy_energy = None\n"
        f"{indent}    policy_comment = None\n"
        f"{indent}if policy_strategy:\n"
        f"{indent}    print()\n"
        f"{indent}    print('--- Loventre Policy Bridge ---')\n"
        f"{indent}    print(f\"Strategia Loventre: {{policy_strategy}}\");\n"
        f"{indent}    if policy_energy is not None:\n"
        f"{indent}        print(f\"Policy energetica: {{policy_energy}}\");\n"
        f"{indent}    if policy_comment:\n"
        f"{indent}        print(f\"Commento: {{policy_comment}}\");\n"
    )

    new_text = text[:insert_pos] + policy_block + text[insert_pos:]
    path.write_text(new_text, encoding="utf-8")
    changed = True

    if changed:
        print(f"✅ Patch applicata a {path}: sezione 'Loventre Policy Bridge' aggiunta dopo lo Strato Planck–Loventre")
    else:
        print(f"ℹ️  Nessuna modifica effettiva per {path}")


def main() -> None:
    cli_path = Path("loventre_meta_decision_cli.py")
    patch_meta_decision_cli(cli_path)


if __name__ == "__main__":
    main()

