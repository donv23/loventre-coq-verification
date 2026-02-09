from pathlib import Path
import re


def hook_policy_in_engine(path: Path) -> None:
    if not path.exists():
        print(f"⚠️  File non trovato: {path}")
        return

    text = path.read_text(encoding="utf-8")
    changed = False

    if "append_policy_bridge_to_metrics(metrics)" in text:
        print("ℹ️  Hook append_policy_bridge_to_metrics(metrics) già presente nel meta-engine; nessuna modifica.")
        return

    # Cerchiamo una chiamata esistente a append_planck_layer_to_metrics(...)
    pattern = r"^(?P<indent>[ \t]*)append_planck_layer_to_metrics\(metrics[^\n]*\)\s*$"

    def _repl(match: re.Match) -> str:
        indent = match.group("indent")
        original_line = match.group(0)
        new_line = f"{indent}append_policy_bridge_to_metrics(metrics)"
        return original_line + "\n" + new_line

    new_text, n_sub = re.subn(pattern, _repl, text, count=1, flags=re.MULTILINE)

    if n_sub == 1:
        path.write_text(new_text, encoding="utf-8")
        changed = True
        print("✅ Hook append_policy_bridge_to_metrics(metrics) aggiunto dopo append_planck_layer_to_metrics(metrics)")
    else:
        print("⚠️  Nessuna riga append_planck_layer_to_metrics(metrics) trovata; hook non inserito.")
        changed = False

    if changed:
        print(f"✅ Patch applicata a {path}")
    else:
        print(f"ℹ️  Nessuna modifica effettiva per {path}")


def main() -> None:
    engine_path = Path("loventre_meta_decision_engine.py")
    hook_policy_in_engine(engine_path)


if __name__ == "__main__":
    main()

