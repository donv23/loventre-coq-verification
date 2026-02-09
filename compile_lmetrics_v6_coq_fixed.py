import subprocess
from pathlib import Path

# Directory dei moduli Coq generati
coq_dir = Path("Coq_IO/LMetrics_v6")

# Wrapper coqc (modifica se usi uno specifico wrapper)
coqc_cmd = "coqc"  # o "./scripts/coqc_lov" se usi il wrapper del progetto

# Lista di tutti i file .v
v_files = sorted(coq_dir.glob("*.v"))

for v_file in v_files:
    print(f"Compilando {v_file} ...")
    result = subprocess.run([coqc_cmd, str(v_file)], capture_output=True, text=True)
    if result.returncode != 0:
        print(f"❌ Errore nella compilazione di {v_file.name}")
        print(result.stderr)
    else:
        print(f"✔ Compilazione riuscita: {v_file.name}")

print("Compilazione di tutti i witness v6 completata.")

