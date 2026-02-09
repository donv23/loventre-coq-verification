from pathlib import Path

path = Path("loventre_global_profile_lab.py")
code = path.read_text()


def add_mean_risk_block(code: str, family_tag: str) -> str:
    header_risk = f"=== Distribuzione rischio ({family_tag}) ==="
    if f"Media risk_index ({family_tag})" in code:
        print(f"ℹ️  Media risk_index per {family_tag} già presente, nessuna modifica.")
        return code

    lines = code.splitlines()

    # 1) trova l'header della distribuzione rischio
    header_idx = None
    for i, line in enumerate(lines):
        if header_risk in line:
            header_idx = i
            break

    if header_idx is None:
        print(f"⚠️  Header rischio per {family_tag} non trovato, skip.")
        return code

    # 2) trova la riga che chiama la distribuzione su risk_class
    risk_call_idx = None
    for j in range(header_idx + 1, min(header_idx + 10, len(lines))):
        if "risk_class" in lines[j] and "(" in lines[j]:
            risk_call_idx = j
            break

    if risk_call_idx is None:
        print(f"⚠️  Nessuna chiamata di distribuzione risk_class trovata per {family_tag}, skip.")
        return code

    risk_call_line = lines[risk_call_idx].strip()

    # Estrai l'espressione del "dataset" (primo argomento della funzione)
    open_par = risk_call_line.find("(")
    comma = risk_call_line.find(",", open_par + 1)
    if open_par == -1 or comma == -1:
        print(f"⚠️  Impossibile parsare la riga di distribuzione rischio per {family_tag}, skip.")
        return code

    dataset_expr = risk_call_line[open_par + 1 : comma].strip()

    # 3) trova il "Dettaglio istanze ..." per inserire il blocco subito prima
    detail_header = f"=== Dettaglio istanze {family_tag} ==="
    detail_idx = None
    for k, line in enumerate(lines):
        if detail_header in line:
            detail_idx = k
            break

    if detail_idx is None:
        print(f"⚠️  Header 'Dettaglio istanze {family_tag}' non trovato, skip.")
        return code

    detail_line = lines[detail_idx]
    indent = detail_line[: len(detail_line) - len(detail_line.lstrip())]

    # 4) costruisce il blocco per la media di risk_index + clima
    blk = [
        f'{indent}# Sintesi rischio (media risk_index) per {family_tag}',
        f"{indent}try:",
        f"{indent}    _risk_source = {dataset_expr}",
        f"{indent}    values = []",
        f'{indent}    # Supporta sia DataFrame con colonna "risk_index" che liste di dict metriche',
        f"{indent}    try:",
        f'{indent}        cols = getattr(_risk_source, "columns", None)',
        f'{indent}        if cols is not None and "risk_index" in cols:',
        f'{indent}            values = [v for v in _risk_source["risk_index"] if v is not None]',
        f"{indent}    except Exception:",
        f"{indent}        pass",
        f"{indent}    if not values and isinstance(_risk_source, list):",
        f"{indent}        for _m in _risk_source:",
        f'{indent}            if isinstance(_m, dict) and "risk_index" in _m and _m["risk_index"] is not None:',
        f"{indent}                values.append(_m['risk_index'])",
        f"{indent}    if values:",
        f"{indent}        _mean_risk = sum(values) / len(values)",
        f'{indent}        print(f"Media risk_index ({family_tag}): {{_mean_risk:.2f}}/10")',
        f"{indent}        if _mean_risk >= 7.5:",
        f'{indent}            clima = "quasi-buco-nero"',
        f"{indent}        elif _mean_risk >= 5.0:",
        f'{indent}            clima = "forte"',
        f"        else:",
        f'{indent}            clima = "moderato"',
        f'{indent}        print(f"Clima di rischio NP_like-critico ({family_tag}): {{clima}}.")',
        f"{indent}except Exception as e:",
        f'{indent}    print("Impossibile calcolare la media risk_index ({family_tag}):", e)',
        "",
    ]

    new_lines = lines[:detail_idx] + blk + lines[detail_idx:]
    print(f"✅ Aggiunta media risk_index per {family_tag}.")
    return "\n".join(new_lines)


code = add_mean_risk_block(code, "TSP_crit_n")
code = add_mean_risk_block(code, "SAT_crit_n")

path.write_text(code)
print("🏁 Patch media risk_index famiglie critiche completata.")

