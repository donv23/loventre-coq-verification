from pathlib import Path

targets = [
    "loventre_meta_decision_cli.py",
    "loventre_meta_decision_engine.py",
]

for fname in targets:
    path = Path(fname)
    if not path.exists():
        continue

    code = path.read_text()
    if "[WARN] Loventre Policy Bridge non disponibile" not in code:
        continue

    # Sostituisce la riga di warning con un fallback silenzioso
    new_code = code.replace(
        'print(f"[WARN] Loventre Policy Bridge non disponibile: {e}")',
        'pass  # Loventre Policy Bridge opzionale: fallback silenzioso'
    )

    if new_code != code:
        path.write_text(new_code)
        print(f"✅ Patch applicata in {fname}: warning Policy Bridge silenziato.")
    else:
        print(f"ℹ️ Nessuna sostituzione in {fname} (pattern non trovato con replace esatto).")

