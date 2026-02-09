from pathlib import Path

path = Path("loventre_meta_decision_engine.py")
code = path.read_text()

old_block = (
    "    # Se i lab non hanno ancora massa, ritorniamo invariati.\n"
    "    if mass_mean is None or inertial_idx is None:\n"
    "\n"
    "\n"
    "    # Regimi di massa / inerzia (soglie volutamente semplici e interpretabili).\n"
)

new_block = (
    "    # Se i lab non hanno ancora massa, ritorniamo invariati.\n"
    "    if mass_mean is None or inertial_idx is None:\n"
    "        return metrics\n"
    "\n"
    "    # Regimi di massa / inerzia (soglie volutamente semplici e interpretabili).\n"
)

if old_block in code:
    code = code.replace(old_block, new_block)
    path.write_text(code)
    print("✅ Patch applicata: early-return ripristinato quando mancano i dati di massa.")
else:
    print("⚠️ Block atteso non trovato, nessuna modifica eseguita.")

