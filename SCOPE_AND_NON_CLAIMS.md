# Scope and Non-Claims

This repository (`loventre-coq-verification`) contains a **formal Coq verification**
of a mathematical framework referred to as the *Loventre Model of Computational Phases*.

The purpose of this document is to state **explicitly and unambiguously**:
- what this repository **does** establish,
- what it **does not** claim,
- and how residual assumptions are **localized and governed**.

---

## 1. What This Repository Establishes

The repository provides:

1. A formally verified **abstract model** in which computational instances
   are classified according to internal structural predicates
   (e.g. `P_like`, `P_like_accessible`, `NP_like_black_hole`).

2. A **non-trivial phase separation** inside the model, proven via Coq,
   between distinct classes of instances defined by:
   - geometric / structural metrics,
   - accessibility constraints,
   - and horizon-like predicates.

3. A **governed epistemic structure** in which:
   - all proved properties are constructive or explicitly axiomatized,
   - all non-proved existence claims are isolated and labeled,
   - no property is defined by negation of an unproven claim.

4. A frozen, auditable state of the formal development,
   identified by the tag `v4-freeze-2026-01-04`,
   ensuring reproducibility and stable evaluation.

---

## 2. What This Repository Does NOT Claim

In particular, this repository **does not claim**:

- A proof of **P ≠ NP** in the classical sense.
- Any statement about **Turing machines, RAM models, or standard complexity classes**
  beyond internal abstractions defined in the model.
- Any empirical or physical interpretation of the constructs used.
- Any universality or completeness with respect to existing complexity theory.

All results are **internal to the Loventre model** and should be read as such.

---

## 3. Localization of Assumptions (Epistemic Governance)

The development follows an explicit epistemic ladder:

- **A1** — Definitions and purely formal constructions.
- **A2** — Theorems proven constructively in Coq.
- **A3** — Explicitly declared existence assumptions,
  localized in dedicated modules and never used implicitly.

In particular, the existence of certain
`P_like_accessible` profiles is treated as an **A3 assumption**:
- it is *not* derived by negation,
- it is *not* hidden in definitions,
- it is *not* required for the core separation result.

This prevents circularity and ensures that the logical status
of each result is transparent.

---

## 4. Scope of Evaluation

A correct evaluation of this repository should therefore focus on:

- internal consistency of definitions,
- correctness of Coq proofs,
- absence of hidden assumptions,
- clarity of the separation between proved results and declared hypotheses.

Any critique based on claims **explicitly excluded above**
falls outside the intended scope of this work.

---

## 5. Separation from Algorithmic or Numerical Components

This repository deliberately excludes:
- numerical simulations,
- algorithmic engines,
- heuristic or experimental components.

Such elements, when they exist, are maintained separately
and are **not required** to validate the formal results presented here.

---

## 6. Status

This document is part of the **v4 epistemic freeze**.
No further claims are intended to be added to this repository.

