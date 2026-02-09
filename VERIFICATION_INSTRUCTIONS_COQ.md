# Loventre v3 — Coq Verification Instructions

## Scope

This repository contains a **formal Coq verification** of the Loventre v3 theorem.

Only the Coq files are relevant for verification.

Any Python code present in the broader project is:
- auxiliary
- non-normative
- NOT part of the proof

---

## Canonical build command

The **only supported verification command** is:

    ./coqc_all_v3.sh

This script compiles all Coq files in the correct order and must terminate with:

    === BUILD OK (GREEN) ===

---

## Assumptions and axioms

All axioms used by the theory are explicitly documented in:

    LOVENTRE_AXIOMS_v3_SEED_2025-12.md

No hidden assumptions are present.

---

## What is verified

- Internal class separation in the Loventre v3 model
- Structural properties (curvature, asymmetry, barriers)
- JSON bridge coherence

---

## What is NOT claimed

- No claim about classical P ≠ NP
- No reliance on simulations
- No external computational assumptions

---

## Reproducibility

The verification is self-contained and reproducible
given a standard Coq installation compatible with this repository.

