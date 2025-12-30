# Loventre Coq Verification — Formal Core

This repository contains the **public, minimal, and explicitly axiomatised Coq core**
of the Loventre framework.

The goal of this repository is **verification**, not interpretation.

---

## Scope

The current tagged release **v1.0-formal-core** provides:

- a small Coq development formalising a **geometric separation principle**
- an explicit list of **axioms and semantic assumptions**
- a structure designed to be **auditable, reproducible, and citable**

No claims are made here about classical P vs NP.

---

## Repository Structure

- `src/`  
  Coq sources.  
  In particular:
  - `Loventre_Geometric_Separation.v` formalises a geometric separation result
    under explicit axioms.

- `axioms/`  
  Human-readable documentation of the axioms and semantic assumptions
  used by the formal core:
  - `LOVENTRE_AXIOMS_v3_SEED_2025-12.md`

---

## What this repository is NOT

- It is **not** a proof of P ≠ NP in the classical sense.
- It is **not** an experimental or numerical implementation.
- It does **not** contain heuristic, probabilistic, or empirical claims.

All such aspects belong to **separate repositories or layers**.

---

## Reproducibility

The Coq files in `src/` compile with a standard Coq installation
(8.18 tested), without requiring external plugins.

The tag:


