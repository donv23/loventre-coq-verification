from pathlib import Path

path = Path("loventre_global_profile_lab.py")
code = path.read_text()


def add_risk_block_for_family(code: str, family_tag: str) -> str:
    """
    Aggiunge una sezione 'Distribuzione rischio (family_tag)' usando
    la stessa chiamata che stampa la distribuzione di meta_label,
    semplicemente sostituendo 'meta_label' con 'risk_class' e
    avvolgendola in un try/except.
    """
    header_risk = f"=== Distribuzione rischio ({family_tag}) ==="
    if header_risk in code:
        print(f"ℹ️  Sezione rischio per {family_tag} già presente, nessuna modifica.")
        return code

    lines = code.splitlines()

    # 1) Trova il blocco meta_label per questa famiglia
    header_meta = f"=== Distribuzione meta_label ({family_tag}) ==="
    meta_header_idx = None
    for i, line in enumerate(lines):
        if header_meta in line:
            meta_header_idx = i
            break

    if meta_header_idx is None:
        print(f"⚠️  Header meta_label per {family_tag} non trovato, skip.")
        return code

    # 2) Trova la riga che chiama la distribuzione su 'meta_label'
    meta_call_idx = None
    for j in range(meta_header_idx + 1, min(meta_header_idx + 15, len(lines))):
        if "meta_label" in lines[j] and "(" in lines[j] and ")" in lines[j]:
            meta_call_idx = j
            break

    if meta_call_idx is None:
        print(f"⚠️  Nessuna chiamata di distribuzione meta_label trovata per {family_tag}, skip.")
        return code

    meta_line = lines[meta_call_idx]
    risk_line = meta_line.replace("meta_label", "risk_class")

    # 3) Trova dove inserire il blocco rischio: subito prima di "Dettaglio istanze ..."
    detail_header = f"=== Dettaglio istanze {family_tag} ==="
    detail_idx = None
    for k, line in enumerate(lines):
        if detail_header in line:
            detail_idx = k
            break

    if detail_idx is None:
        print(f"⚠️  Header 'Dettaglio istanze {family_tag}' non trovato, skip.")
        return code

    # Indent della sezione corrente (usiamo quello del dettaglio, per stare nel blocco giusto)
    detail_line = lines[detail_idx]
    indent = detail_line[: len(detail_line) - len(detail_line.lstrip())]

    # Costruisce il blocco rischio, con try/except per evitare crash se risk_class non esiste
    risk_block_lines = [
        f'{indent}print("\\n=== Distribuzione rischio ({family_tag}) ===")',
        f"{indent}try:",
        f"{indent}    {risk_line.strip()}",
        f"{indent}except Exception as e:",
        f'{indent}    print("Nessuna informazione di rischio (risk_class) disponibile per {family_tag}:", e)',
        "",
    ]

    # Inserisce il blocco prima del dettaglio
    new_lines = lines[:detail_idx] + risk_block_lines + lines[detail_idx:]
    print(f"✅ Aggiunta sezione rischio per {family_tag}.")
    return "\n".join(new_lines)


# Applica per entrambe le famiglie critiche
code = add_risk_block_for_family(code, "TSP_crit_n")
code = add_risk_block_for_family(code, "SAT_crit_n")

path.write_text(code)
print("🏁 Patch completata su loventre_global_profile_lab.py.")
from pathlib import Path

path = Path("loventre_global_profile_lab.py")
code = path.read_text()


def add_risk_block_for_family(code: str, family_tag: str) -> str:
    """
    Aggiunge una sezione 'Distribuzione rischio (family_tag)' usando
    la stessa chiamata che stampa la distribuzione di meta_label,
    semplicemente sostituendo 'meta_label' con 'risk_class' e
    avvolgendola in un try/except.
    """
    header_risk = f"=== Distribuzione rischio ({family_tag}) ==="
    if header_risk in code:
        print(f"ℹ️  Sezione rischio per {family_tag} già presente, nessuna modifica.")
        return code

    lines = code.splitlines()

    # 1) Trova il blocco meta_label per questa famiglia
    header_meta = f"=== Distribuzione meta_label ({family_tag}) ==="
    meta_header_idx = None
    for i, line in enumerate(lines):
        if header_meta in line:
            meta_header_idx = i
            break

    if meta_header_idx is None:
        print(f"⚠️  Header meta_label per {family_tag} non trovato, skip.")
        return code

    # 2) Trova la riga che chiama la distribuzione su 'meta_label'
    meta_call_idx = None
    for j in range(meta_header_idx + 1, min(meta_header_idx + 15, len(lines))):
        if "meta_label" in lines[j] and "(" in lines[j] and ")" in lines[j]:
            meta_call_idx = j
            break

    if meta_call_idx is None:
        print(f"⚠️  Nessuna chiamata di distribuzione meta_label trovata per {family_tag}, skip.")
        return code

    meta_line = lines[meta_call_idx]
    risk_line = meta_line.replace("meta_label", "risk_class")

    # 3) Trova dove inserire il blocco rischio: subito prima di "Dettaglio istanze ..."
    detail_header = f"=== Dettaglio istanze {family_tag} ==="
    detail_idx = None
    for k, line in enumerate(lines):
        if detail_header in line:
            detail_idx = k
            break

    if detail_idx is None:
        print(f"⚠️  Header 'Dettaglio istanze {family_tag}' non trovato, skip.")
        return code

    # Indent della sezione corrente (usiamo quello del dettaglio, per stare nel blocco giusto)
    detail_line = lines[detail_idx]
    indent = detail_lin_

