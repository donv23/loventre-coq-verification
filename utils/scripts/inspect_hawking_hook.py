from pathlib import Path
import sys

path = Path("loventre_meta_decision_engine.py")
if not path.exists():
    print("File loventre_meta_decision_engine.py non trovato.")
    sys.exit(1)

code = path.read_text(encoding="utf-8")
lines = code.splitlines()

print("=== LINEE CON append_hawking_layer_to_metrics ===")
for i, line in enumerate(lines, start=1):
    if "append_hawking_layer_to_metrics" in line:
        print(f"{i:4d}: {line}")

print("\n=== LINEE CON append_planck_layer_to_metrics ===")
for i, line in enumerate(lines, start=1):
    if "append_planck_layer_to_metrics" in line:
        print(f"{i:4d}: {line}")

print("\n=== BLOCCO DEF append_hawking_layer_to_metrics (linee 660-700) ===")
for i in range(659, 700):
    if 0 <= i < len(lines):
        print(f"{i+1:4d}: {lines[i]}")

print("\n=== CODA DI meta_decide_instance_with_mass (ultime ~80 righe della funzione) ===")
start_idx = None
for i, line in enumerate(lines):
    if "def meta_decide_instance_with_mass" in line:
        start_idx = i
        break

if start_idx is None:
    print("Def meta_decide_instance_with_mass NON trovata.")
    sys.exit(0)

# prendiamo un blocco di 220 righe dopo l'inizio della funzione
tail = lines[start_idx : start_idx + 220]
tail_to_print = tail[-80:]  # ultime ~80 righe
for i, line in enumerate(tail_to_print, start=1):
    print(f"{i:4d}: {line}")

