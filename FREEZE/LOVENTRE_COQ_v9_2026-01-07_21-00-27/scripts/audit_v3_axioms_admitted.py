#!/usr/bin/env python3
from __future__ import annotations

import re
from pathlib import Path
from datetime import datetime

ROOT = Path(__file__).resolve().parents[1]

GREEN_FILES = [
    "01_Core/Loventre_Core_Prelude.v",

    "02_Advanced/Geometry/Loventre_Metrics_Bus.v",
    "02_Advanced/Geometry/Loventre_LMetrics_Structure.v",
    "02_Advanced/Geometry/Loventre_LMetrics_JSON_Witness.v",
    "02_Advanced/Geometry/Loventre_LMetrics_Phase_Predicates.v",
    "02_Advanced/Geometry/Loventre_LMetrics_Existence_Summary.v",

    "03_Main/Loventre_LMetrics_Policy_Specs.v",
    "03_Main/Loventre_LMetrics_Separation_Program.v",
    "03_Main/Loventre_Theorem_v3_P_vs_NP_like.v",
    "03_Main/Loventre_Theorem_v3_Citable_Prop.v",
    "03_Main/Test_Loventre_Theorem_v3_All.v",
]

PATTERNS = [
    ("Admitted", re.compile(r"(?m)^\s*Admitted\b")),
    ("admit.", re.compile(r"(?mi)^\s*admit\.\s*$")),
    ("Axiom", re.compile(r"(?m)^\s*Axiom\b")),
    ("Hypothesis", re.compile(r"(?m)^\s*Hypothesis\b")),
]

def line_number_at(text: str, idx: int) -> int:
    return text.count("\n", 0, idx) + 1

def main() -> int:
    hits = []
    missing = []

    for rel in GREEN_FILES:
        vf = ROOT / rel
        if not vf.exists():
            missing.append(rel)
            continue

        try:
            txt = vf.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            txt = vf.read_text(encoding="latin-1")

        lines = txt.splitlines()

        for tag, rgx in PATTERNS:
            for m in rgx.finditer(txt):
                ln = line_number_at(txt, m.start())
                line = lines[ln - 1].rstrip() if 0 <= ln - 1 < len(lines) else ""
                hits.append((rel, ln, tag, line))

    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    out_dir = ROOT / "98_AUDIT"
    out_dir.mkdir(parents=True, exist_ok=True)
    out_file = out_dir / f"AUDIT_V3_GREEN_CHAIN_{ts}.txt"

    with out_file.open("w", encoding="utf-8") as f:
        f.write("AUDIT V3 — GREEN CHAIN ONLY\n")
        f.write(f"ROOT = {ROOT}\n")
        f.write(f"TIMESTAMP = {ts}\n\n")

        if missing:
            f.write("MISSING FILES:\n")
            for rel in missing:
                f.write(f"- {rel}\n")
            f.write("\n")

        if not hits:
            f.write("OK: nessun Axiom/Admitted/Hypothesis/admit. nella GREEN CHAIN.\n")
        else:
            f.write(f"TROVATI {len(hits)} HIT nella GREEN CHAIN:\n\n")
            for rel, ln, tag, line in hits:
                f.write(f"{rel}:{ln}: {tag}: {line}\n")

    print(str(out_file))
    if missing:
        print(f"ATTENZIONE: {len(missing)} file mancanti (vedi report).")
    if not hits:
        print("OK: nessun Axiom/Admitted/Hypothesis/admit. nella GREEN CHAIN.")
    else:
        print(f"TROVATI {len(hits)} HIT nella GREEN CHAIN (vedi report).")

    return 0

if __name__ == "__main__":
    raise SystemExit(main())

