from pathlib import Path
import re

path = Path("loventre_global_profile_lab.py")
code = path.read_text()

# --- TSP_crit_n ---

pattern_tsp = (
    r'        if values:\n'
    r'(?:.*\n)*?'
    r'    except Exception as e:\n'
    r'        print\("Impossibile calcolare la media risk_index \(TSP_crit_n\):", e\)\n'
)

new_tsp = (
    '        if values:\n'
    '            _mean_risk = sum(values) / len(values)\n'
    '            print(f"Media risk_index (TSP_crit_n): {_mean_risk:.2f}/10")\n'
    '            if _mean_risk >= 7.5:\n'
    '                clima = "quasi-buco-nero"\n'
    '            elif _mean_risk >= 5.0:\n'
    '                clima = "forte"\n'
    '            else:\n'
    '                clima = "moderato"\n'
    '            print(f"Clima di rischio NP_like-critico (TSP_crit_n): {clima}.")\n'
    '    except Exception as e:\n'
    '        print("Impossibile calcolare la media risk_index (TSP_crit_n):", e)\n'
)

code_new, n_tsp = re.subn(pattern_tsp, new_tsp + "\n", code, flags=re.DOTALL)
print("Blocchi TSP_crit_n sostituiti:", n_tsp)

# --- SAT_crit_n ---

pattern_sat = (
    r'        if values:\n'
    r'(?:.*\n)*?'
    r'    except Exception as e:\n'
    r'        print\("Impossibile calcolare la media risk_index \(SAT_crit_n\):", e\)\n'
)

new_sat = (
    '        if values:\n'
    '            _mean_risk = sum(values) / len(values)\n'
    '            print(f"Media risk_index (SAT_crit_n): {_mean_risk:.2f}/10")\n'
    '            if _mean_risk >= 7.5:\n'
    '                clima = "quasi-buco-nero"\n'
    '            elif _mean_risk >= 5.0:\n'
    '                clima = "forte"\n'
    '            else:\n'
    '                clima = "moderato"\n'
    '            print(f"Clima di rischio NP_like-critico (SAT_crit_n): {clima}.")\n'
    '    except Exception as e:\n'
    '        print("Impossibile calcolare la media risk_index (SAT_crit_n):", e)\n'
)

code_new, n_sat = re.subn(pattern_sat, new_sat + "\n", code_new, flags=re.DOTALL)
print("Blocchi SAT_crit_n sostituiti:", n_sat)

path.write_text(code_new)
print("✅ Patch blocchi media risk_index applicata.")

