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

    # Pattern problematico: chain con ';' prima dei bullet
    old = (
        "  inversion Hxy; subst;\n"
        "  destruct distinct_abc as [Dab [Dbc Dac]];\n"
    )
    new = (
        "  inversion Hxy; subst.\n"
        "  all: destruct distinct_abc as [Dab [Dbc Dac]].\n"
    )

    if new in block:
        print("OK: semicolon/bullets patch already applied (nothing to do).")
        return

    if old not in block:
        # fallback: prova a correggere almeno il ';' finale del destruct
        old2 = "  destruct distinct_abc as [Dab [Dbc Dac]];\n"
        new2 = "  destruct distinct_abc as [Dab [Dbc Dac]].\n"
        if old2 in block:
            block2 = block.replace(old2, new2, 1)
            txt2 = txt[:i] + block2 + txt[j:]
            TARGET.write_text(txt2, encoding="utf-8")
            print("OK: patched (removed trailing ';' after destruct distinct_abc).")
            return
        raise SystemExit("ERROR: cannot find expected tactic chain to patch inside terminal_isolated")

    block2 = block.replace(old, new, 1)
    txt2 = txt[:i] + block2 + txt[j:]
    TARGET.write_text(txt2, encoding="utf-8")
    print("OK: patched terminal_isolated (fixed ';' before bullets using all:).")

if __name__ == "__main__":
    main()

