#!/usr/bin/env python3

"""
Loventre Export — Coq Template (Canvas 29)
"""

import sys
import json


def load_export_json(path: str) -> dict:
    """
    Reads a witness export JSON-like file produced by loventre_pipeline.
    Returns a dict of fields.
    """
    out = {}
    with open(path, "r") as f:
        for line in f:
            line = line.strip()
            if "=" in line:
                key, val = line.split("=", 1)
                out[key] = val
    return out


def render_coq_template(exp: dict) -> str:
    """
    Convert witness export dict into canonical Coq instantiation.
    """
    return f"""
(*
  Loventre Witness Export → Coq Template
*)

Definition LoventreWitness_Fingerprint : string := "{exp['FINGERPRINT']}".

Record LoventreWitness_Record := mkWitness {{
  w_type : string;
  w_decision : string;
  w_lmetrics_type : string;
  w_score : string;
  w_color : string;
}}.

Definition LoventreWitness_Instance : LoventreWitness_Record :=
  mkWitness
    "{exp['TYPE']}"
    "{exp['DECISION']}"
    "{exp['LMETRICS_TYPE']}"
    "{exp['SCORE']}"
    "{exp['COLOR']}".
"""


def main():
    if len(sys.argv) != 3:
        print("Usage: python3 loventre_export_coq_template.py input_export.json output.v")
        sys.exit(1)

    infile = sys.argv[1]
    outfile = sys.argv[2]

    exp = load_export_json(infile)
    coq = render_coq_template(exp)

    with open(outfile, "w") as f:
        f.write(coq)

    print(f"[OK] Coq template generated → {outfile}")


if __name__ == "__main__":
    main()

