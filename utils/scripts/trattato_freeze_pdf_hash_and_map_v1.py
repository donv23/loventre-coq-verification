#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Trattato Freeze Kit v1:
- Converte DOCX -> PDF (LibreOffice/soffice headless)
- Calcola SHA256 per DOCX+PDF
- Aggiorna TRATTATO_HASH_v1.txt
- Aggiorna TRATTATO_CITATION_MAP_v1.md chiedendo all'utente i range pagine (p.X–p.Y)
  senza editing manuale: input guidato e deterministico.

Uso:
  python3 scripts/trattato_freeze_pdf_hash_and_map_v1.py
"""

from __future__ import annotations
import hashlib
import os
import re
import subprocess
from pathlib import Path

ROOT = Path.cwd()

DOCX = ROOT / "01_Trattato" / "Trattato_sulla_Geometria_Discreta_di_Orientamento_v1.0.docx"
PDF  = ROOT / "01_Trattato" / "Trattato_sulla_Geometria_Discreta_di_Orientamento_v1.0.pdf"

CIT_MAP = ROOT / "01_Trattato" / "TRATTATO_CITATION_MAP_v1.md"
HASH_TXT = ROOT / "01_Trattato" / "TRATTATO_HASH_v1.txt"

def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()

def require_exists(p: Path, label: str) -> None:
    if not p.exists():
        raise FileNotFoundError(f"[FATAL] Missing {label}: {p}")

def run_soffice_convert(docx_path: Path, outdir: Path) -> None:
    # Convert to PDF using LibreOffice headless
    # NOTE: LibreOffice names output as <docx_stem>.pdf by default in outdir.
    cmd = [
        "soffice",
        "--headless",
        "--nologo",
        "--nofirststartwizard",
        "--convert-to",
        "pdf",
        "--outdir",
        str(outdir),
        str(docx_path),
    ]
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(
            "[FATAL] soffice conversion failed.\n"
            f"STDOUT:\n{r.stdout}\nSTDERR:\n{r.stderr}\n"
        )

def ensure_pdf_named(docx_path: Path, desired_pdf: Path) -> None:
    # LibreOffice creates <stem>.pdf; rename to desired name if needed.
    produced = desired_pdf.parent / (docx_path.stem + ".pdf")
    if not produced.exists():
        raise FileNotFoundError(f"[FATAL] Expected PDF not found after conversion: {produced}")
    if produced.resolve() != desired_pdf.resolve():
        if desired_pdf.exists():
            desired_pdf.unlink()
        produced.rename(desired_pdf)

def update_hash_file(docx_path: Path, pdf_path: Path, hash_txt: Path) -> None:
    docx_hash = sha256_file(docx_path)
    pdf_hash = sha256_file(pdf_path)
    lines = []
    lines.append("TRATTATO_VERSION: v1.0")
    lines.append("HASH_ALGO: SHA256")
    lines.append(f"SHA256  {docx_hash}  01_Trattato/{docx_path.name}")
    lines.append(f"SHA256  {pdf_hash}  01_Trattato/{pdf_path.name}")
    lines.append("")
    hash_txt.write_text("\n".join(lines), encoding="utf-8")

def prompt_page_ranges_update(cit_map_path: Path) -> None:
    """
    Aggiorna le righe con placeholder 'p.__–p.__' chiedendo input all'utente.
    Regola input:
      - Inserisci 'X-Y' (es. 17-19) oppure 'X' (singola pagina)
      - Invio vuoto = lascia invariato (resta __)
    """
    txt = cit_map_path.read_text(encoding="utf-8")

    # Trova righe del tipo: "§5.2 ... → p.__–p.__"
    pattern = re.compile(r"(→\s*p\.__–p\.__)")
    if not pattern.search(txt):
        # Nessun placeholder: niente da fare.
        return

    # Trova tutte le righe candidate e costruisci prompt con contesto minimo
    lines = txt.splitlines()
    out_lines = []
    for line in lines:
        if "→ p.__–p.__" in line:
            # Mostra la riga "sezione → placeholder" e chiedi page range
            print("\n[PAGE MAP] Riga da completare:")
            print(line)
            user = input("Inserisci pagine PDF (X-Y oppure X) o ENTER per lasciare __: ").strip()
            if user == "":
                out_lines.append(line)
                continue
            m = re.fullmatch(r"(\d+)\s*-\s*(\d+)", user)
            if m:
                a = int(m.group(1)); b = int(m.group(2))
                if a <= 0 or b <= 0 or b < a:
                    print("[WARN] Range non valido: mantengo __.")
                    out_lines.append(line)
                else:
                    newline = line.replace("→ p.__–p.__", f"→ p.{a}–p.{b}")
                    out_lines.append(newline)
                continue
            m2 = re.fullmatch(r"(\d+)", user)
            if m2:
                a = int(m2.group(1))
                if a <= 0:
                    print("[WARN] Pagina non valida: mantengo __.")
                    out_lines.append(line)
                else:
                    newline = line.replace("→ p.__–p.__", f"→ p.{a}–p.{a}")
                    out_lines.append(newline)
                continue
            print("[WARN] Input non riconosciuto: mantengo __.")
            out_lines.append(line)
        else:
            out_lines.append(line)

    cit_map_path.write_text("\n".join(out_lines) + "\n", encoding="utf-8")

def main() -> None:
    print("[INFO] Trattato Freeze Kit v1 — start")
    require_exists(DOCX, "DOCX")
    require_exists(CIT_MAP, "Citation Map")
    # Hash file può esistere o meno; lo riscriviamo.

    # Step 1: convert DOCX->PDF
    print("[INFO] Converto DOCX → PDF via LibreOffice (soffice)...")
    try:
        subprocess.run(["soffice", "--version"], check=True, capture_output=True, text=True)
    except Exception as e:
        raise RuntimeError(
            "[FATAL] 'soffice' non disponibile. "
            "Installa LibreOffice oppure usa la procedura manuale (Canvas 176 §4)."
        ) from e

    run_soffice_convert(DOCX, DOCX.parent)
    ensure_pdf_named(DOCX, PDF)
    print(f"[OK] PDF creato: {PDF}")

    # Step 2: write hashes
    print("[INFO] Calcolo SHA256 e aggiorno TRATTATO_HASH_v1.txt ...")
    update_hash_file(DOCX, PDF, HASH_TXT)
    print(f"[OK] Hash scritto: {HASH_TXT}")

    # Step 3: update citation map placeholders
    print("[INFO] Aggiorno TRATTATO_CITATION_MAP_v1.md (pagine) via prompt guidato...")
    prompt_page_ranges_update(CIT_MAP)
    print(f"[OK] Citation map aggiornata: {CIT_MAP}")

    print("[DONE] Trattato freeze completato (PDF+hash+map).")

if __name__ == "__main__":
    main()

