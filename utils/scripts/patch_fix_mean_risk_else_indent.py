from pathlib import Path

path = Path("loventre_global_profile_lab.py")
code = path.read_text()

old = '        else:\n                clima = "moderato"'
new = '            else:\n                clima = "moderato"'

if old in code:
    code = code.replace(old, new)
    path.write_text(code)
    print("✅ Re-indented 'else' blocks for clima = 'moderato'.")
else:
    print("ℹ️ Pattern 'else/clima=moderato' non trovato, nessuna modifica.")

