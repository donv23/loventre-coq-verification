from pathlib import Path

path = Path("loventre_global_profile_lab.py")
code = path.read_text()

old_tsp = '=== Dettaglio istanze TSP_crit_n ===")'
new_tsp = 'print("=== Dettaglio istanze TSP_crit_n ===")'

old_sat = '=== Dettaglio istanze SAT_crit_n ===")'
new_sat = 'print("=== Dettaglio istanze SAT_crit_n ===")'

changed = False

if old_tsp in code:
    code = code.replace(old_tsp, new_tsp)
    print("✅ Fix header dettaglio TSP_crit_n.")
    changed = True
else:
    print("ℹ️ Header TSP_crit_n già corretto o non trovato.")

if old_sat in code:
    code = code.replace(old_sat, new_sat)
    print("✅ Fix header dettaglio SAT_crit_n.")
    changed = True
else:
    print("ℹ️ Header SAT_crit_n già corretto o non trovato.")

if changed:
    path.write_text(code)
    print("🏁 patch_fix_detail_headers: modifiche salvate.")
else:
    print("🏁 patch_fix_detail_headers: nessuna modifica necessaria.")

