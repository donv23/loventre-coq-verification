from pathlib import Path
import re

def patch_file(path: Path):
    text = path.read_text(encoding="utf-8")

    # Trova il punto in cui viene chiamato append_planck_layer_to_metrics (subito dopo inseriamo il Bridge)
    pattern = r"append_planck_layer_to_metrics\s*\(\s*metrics\s*\)"
    if not re.search(pattern, text):
        print("⚠️  Nessuna chiamata a append_planck_layer_to_metrics(metrics) trovata.")
        return

    if "append_policy_bridge_to_metrics(metrics)" in text:
        print("ℹ️  append_policy_bridge_to_metrics(metrics) è già presente, nessuna modifica.")
        return

    new_text = re.sub(
        pattern,
        "append_planck_layer_to_metrics(metrics)\n    append_policy_bridge_to_metrics(metrics)",
        text,
    )

    path.write_text(new_text, encoding="utf-8")
    print("✅ Hook append_policy_bridge_to_metrics inserito dopo append_planck_layer_to_metrics.")
    print(f"✅ Patch applicata a {path}")


def main():
    target = Path("loventre_meta_decision_engine.py")
    if not target.exists():
        print("⚠️  File non trovato.")
        return
    patch_file(target)


if __name__ == "__main__":
    main()

