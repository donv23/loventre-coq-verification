from pathlib import Path
import re


def hook_policy_in_meta_decide(path: Path) -> None:
    if not path.exists():
        print(f"⚠️  File non trovato: {path}")
        return

    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()

    # Trova la definizione di meta_decide_instance_with_mass
    target = "def meta_decide_instance_with_mass"
    start_idx = None
    for i, line in enumerate(lines):
        if target in line:
            start_idx = i
            break

    if start_idx is None:
        print(f"⚠️  Non trovata la funzione {target}")
        return

    # Trova la fine della funzione (prima del prossimo 'def ' a colonna 0 o fine file)
    end_idx = len(lines)
    for j in range(start_idx + 1, len(lines)):
        if lines[j].startswith("def "):
            end_idx = j
            break

    # Controlla se esiste già una chiamata a append_policy_bridge_to_metrics in questo blocco
    for k in range(start_idx, end_idx):
        if "append_policy_bridge_to_metrics(" in lines[k]:
            print("ℹ️  append_policy_bridge_to_metrics(metrics) è già chiamata in meta_decide_instance_with_mass; nessuna modifica.")
            return

    # Trova l'ULTIMA riga 'return metrics' dentro la funzione
    last_return_idx = None
    for k in range(start_idx, end_idx):
        if re.search(r"\breturn\s+metrics\b", lines[k]):
            last_return_idx = k

    if last_return_idx is None:
        print("⚠️  Nessun 'return metrics' trovato in meta_decide_instance_with_mass; nessuna patch applicata.")
        return

    # Usa la stessa indentazione della riga di return
    return_line = lines[last_return_idx]
    indent = return_line[: len(return_line) - len(return_line.lstrip(" \t"))]
    new_line = indent + "append_policy_bridge_to_metrics(metrics)"

    # Inserisci la chiamata PRIMA dell'ultimo return metrics
    lines.insert(last_return_idx, new_line)

    new_text = "\n".join(lines)
    path.write_text(new_text, encoding="utf-8")

    print("✅ Inserita append_policy_bridge_to_metrics(metrics) prima dell'ultimo 'return metrics' in meta_decide_instance_with_mass")
    print(f"✅ Patch applicata a {path}")


def main() -> None:
    engine_path = Path("loventre_meta_decision_engine.py")
    hook_policy_in_meta_decide(engine_path)


if __name__ == "__main__":
    main()

