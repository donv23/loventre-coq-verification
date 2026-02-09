from pathlib import Path

path = Path("loventre_global_profile_lab.py")
code = path.read_text()

lines = code.splitlines()


def rebuild_mean_risk_block(lines, family_tag: str):
    header_risk = f"=== Distribuzione rischio ({family_tag}) ==="
    detail_header = f"=== Dettaglio istanze {family_tag} ==="

    # 1) trova header rischio
    header_idx = None
    for i, line in enumerate(lines):
        if header_risk in line:
            header_idx = i
            break
    if header_idx is None:
        print(f"Header rischio per {family_tag} non trovato, skip.")
        return lines

    # 2) trova riga che chiama la distribuzione su risk_class
    risk_call_idx = None
    for j in range(header_idx + 1, min(header_idx + 15, len(lines))):
        if "risk_class" in lines[j] and "(" in lines[j]:
            risk_call_idx = j
            break
    if risk_call_idx is None:
        print(f"Nessuna chiamata di distribuzione risk_class trovata per {family_tag}, skip.")
        return lines

    risk_call_line = lines[risk_call_idx].strip()
    open_par = risk_call_line.find("(")
    comma = risk_call_line.find(",", open_par + 1)
    if open_par == -1 or comma == -1:
        print(f"Impossibile parsare la riga di distribuzione rischio per {family_tag}, skip.")
        return lines

    dataset_expr = risk_call_line[open_par + 1 : comma].strip()

    # 3) trova header dettaglio
    detail_idx = None
    for k, line in enumerate(lines):
        if detail_header in line:
            detail_idx = k
            break
    if detail_idx is None:
        print(f"Header 'Dettaglio istanze {family_tag}' non trovato, skip.")
        return lines

    # 4) se esiste un vecchio blocco "Sintesi rischio", rimuovilo
    start_idx = detail_idx
    for i in range(detail_idx - 1, max(detail_idx - 40, -1), -1):
        if lines[i].strip().startswith(f"# Sintesi rischio (media risk_index) per {family_tag}"):
            start_idx = i
            break

    # blocco nuovo, top-level, indentazione pulita
    block = [
        f"# Sintesi rischio (media risk_index) per {family_tag}",
        "try:",
        f"    _risk_source = {dataset_expr}",
        "    values = []",
        '    # Supporta sia DataFrame con colonna \"risk_index\" che liste di dict metriche',
        "    try:",
        '        cols = getattr(_risk_source, \"columns\", None)',
        '        if cols is not None and \"risk_index\" in cols:',
        '            values = [v for v in _risk_source[\"risk_index\"] if v is not None]',
        "    except Exception:",
        "        pass",
        "    if not values and isinstance(_risk_source, list):",
        "        for _m in _risk_source:",
        '            if isinstance(_m, dict) and \"risk_index\" in _m and _m[\"risk_index\"] is not None:',
        "                values.append(_m['risk_index'])",
        "    if values:",
        "        _mean_risk = sum(values) / len(values)",
        f'        print(\"Media risk_index ({family_tag}): {{_mean_risk:.2f}}/10\")',
        "        if _mean_risk >= 7.5:",
        '            clima = \"quasi-buco-nero\"',
        "        elif _mean_risk >= 5.0:",
        '            clima = \"forte\"',
        "        else:",
        '            clima = \"moderato\"',
        f'        print(\"Clima di rischio NP_like-critico ({family_tag}): {{clima}}.\")',
        "except Exception as e:",
        f'    print(\"Impossibile calcolare la media risk_index ({family_tag}):\", e)',
        "",
    ]

    new_lines = lines[:start_idx] + block + lines[detail_idx:]
    print(f\"Blocco media risk_index ricostruito per {family_tag}.\")
    return new_lines


lines = rebuild_mean_risk_block(lines, "TSP_crit_n")
lines = rebuild_mean_risk_block(lines, "SAT_crit_n")

path.write_text("\\n".join(lines))
print("Fix indentazione media risk_index famiglie critiche completato.")
from pathlib import Path

path = Path("loventre_global_profile_lab.py")
code = path.read_text()

lines = code.splitlines()


def rebuild_mean_risk_block(lines, family_tag: str):
    header_risk = f"=== Distribuzione rischio ({family_tag}) ==="
    detail_header = f"=== Dettaglio istanze {family_tag} ==="

    # 1) trova header rischio
    header_idx = None
    for i, line in enumerate(lines):
        if header_risk in line:
            header_idx = i
            break
    if header_idx is None:
        print(f"⚠️  Header rischio per {family_tag} non trovato, skip.")
        return lines

    # 2) trova riga che chiama la distribuzione su risk_class
    risk_call_idx = None
    for j in range(header_idx + 1, min(header_idx + 15, len(lines))):
        if "risk_class" in lines[j] and "(" in lines[j]:
            risk_call_idx = j
            break
    if risk_call_idx is None:
        print(f"⚠️  Nessuna chiamata di distribuzione risk_class trovata per {family_tag}, skip.")
        return lines

    risk_call_line = lines[risk_call_idx].strip()
    open_par = risk_call_line.find("(")
    comma = risk_call_line.find(",", open_par + 1)
    if open_par == -1 or comma == -1:
        print(f"⚠️  Impossibile parsare la riga di distribuzione rischio per {family_tag}, skip.")
        return lines

    dataset_expr = risk_call_line[open_par + 1 : comma].strip()

    # 3) trova header dettaglio
    detail_idx = None
    for k, line in enumerate(lines):
        if detail_header in line:
            detail_idx = k
            break
    if detail_idx is None:
        print(f"⚠️  Header 'Dettaglio istanze {family_tag}' non trovato, skip.")
        return lines

    # 4) se esiste un vecchio blocco "Sintesi rischio", rimuovilo
    start_idx = detail_idx
    for i in range(detail_idx - 1, max(detail_idx - 40, -1), -1):
        if lines[i].strip().startswith(f"# Sintesi rischio (media risk_index) per {family_tag}"):
            start_idx = i
            break

    # blocco nuovo, top-level, indentazione pulita
    block = [
        f"# Sintesi rischio (media risk_index) per {family_tag}",
        "try:",
        f"    _risk_source = {dataset_expr}",
        "    values = []",
        '    # Supporta sia DataFrame con colonna "risk_index" che liste di dict metriche',
        "    try:",
        '        cols = getattr(_risk_source, \"columns\", None)',
        '        if cols is not None and \"risk_index\" in cols:',
        '            values = [v for v in _risk_source[\"risk_index\"] if v is not None]',
        "    except Exception:",
        "        pass",
        "    if not values and isinstance(_risk_source, list):",
        "        for _m in _risk_source:",
        '            if isinstance(_m, dict) and \"risk_index\" in _m and _m[\"risk_index\"] is not None:',
        "                values.append(_m['risk_index'])",
        "    if values:",
        "        _mean_risk = sum(values) / len(values)",
        f'        print(f\"Media risk_index ({family_tag}): {{_mean_risk:.2f}}/10\")',
        "        if _mean_risk >= 7.5:",
        '            clima = \"quasi-buco-nero\"',
        "        elif _mean_risk >= 5.0:",
        '            clima = \"forte\"',
        "        else:",
        '            clima = \"moderato\"',
        f'        print(f\"Clima di rischio NP_like-critico ({family_tag}): {{clima}}.\")',
        "except Exception as e:",
        f'    print(\"Impossibile calcolare la media risk_index ({family_tag}):\", e)',
        "",
    ]

    new_lines = lines[:start_idx] + block + lines[detail_idx:]
    print(f"✅ Blocco media risk_index ricostruito_

