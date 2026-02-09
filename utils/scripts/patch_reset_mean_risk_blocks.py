from pathlib import Path

path = Path("loventre_global_profile_lab.py")
code = path.read_text()

for tag in ("TSP_crit_n", "SAT_crit_n"):
    marker = f"# Sintesi rischio (media risk_index) per {tag}"
    detail = f"=== Dettaglio istanze {tag} ==="
    start = code.find(marker)
    end = code.find(detail)
    if start != -1 and end != -1 and end > start:
        print(f"Rimuovo blocco 'Sintesi rischio' per {tag}.")
        code = code[:start] + code[end:]
    else:
        print(f"Nessun blocco da rimuovere per {tag}.")

path.write_text(code)
print("✅ Reset blocchi 'Sintesi rischio' completato.")

