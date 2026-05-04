from __future__ import annotations

import pathlib

ROOT = pathlib.Path("/Users/vincenzoloventre/Desktop/loventre-coq-cycle11-lab")
TARGET = ROOT / "02_Advanced" / "LAB_12_Minimal_Rigidity" / "L12_2_Pairwise" / "CounterModel_Pairwise.v"

def main() -> None:
    if not TARGET.exists():
        raise SystemExit(f"ERROR: file not found: {TARGET}")

    txt = TARGET.read_text(encoding="utf-8")

    key = "Lemma terminal_isolated"
    i = txt.find(key)
    if i < 0:
        raise SystemExit("ERROR: cannot find 'Lemma terminal_isolated' in file")

    j = txt.find("\nQed.", i)
    if j < 0:
        raise SystemExit("ERROR: cannot find end of lemma (Qed.) after terminal_isolated")

    block = txt[i:j]

    old_line = "\n  subst x.\n"
    new_line = "\n  unfold Isolating in Hiso; subst x.\n"

    if new_line in block:
        print("OK: patch already applied (nothing to do).")
        return

    if old_line not in block:
        raise SystemExit("ERROR: cannot find the exact line '  subst x.' inside terminal_isolated block")

    block2 = block.replace(old_line, new_line, 1)
    txt2 = txt[:i] + block2 + txt[j:]

    TARGET.write_text(txt2, encoding="utf-8")
    print("OK: patched terminal_isolated (added unfold Isolating in Hiso before subst).")

if __name__ == "__main__":
    main()

