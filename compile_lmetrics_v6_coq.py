import subprocess
from pathlib import Path

coq_dir = Path("Coq_IO/LMetrics_v6")

# Compilazione di tutti i moduli .v in ordine
for coq_file in sorted(coq_dir.glob("*.v")):
    print(f"Compilando {coq_file} ...")
    result = subprocess.run(["coqc", str(coq_file)], capture_output=True, text=True)
    if result.returncode == 0:
        print(f"✔ {coq_file.stem} compilato correttamente")
    else:
        print(f"❌ Errore nella compilazione di {coq_file.stem}")
        print(result.stderr)
        break

print("\nCompilazione completata.")

