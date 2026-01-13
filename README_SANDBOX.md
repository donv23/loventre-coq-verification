# LOVENTRE — SANDBOX Layer

## Overview

The SANDBOX layer provides **controlled experimental environments**
built on top of the Loventre CANON mathematical core.

SANDBOX modules are designed to:

* explore applications
* test interpretations
* visualize outcomes
* experiment with domain-specific semantics

while remaining **strictly subordinate** to CANON.

SANDBOX is **not** part of the formal core.
It introduces **no axioms**, **no guarantees**, and **no proofs**.

---

## Position in the Architecture

The Loventre theory is organized into three strictly separated layers:

1. **CANON**
   The formally verified mathematical core (Coq, audit-safe).

2. **SANDBOX**
   Experimental and applied interpretations of CANON outcomes.

3. **ENGINE**
   Operational systems that produce concrete informational states.

This repository documents SANDBOX as an **intermediate interpretative layer**.

---

## What SANDBOX Is

SANDBOX modules may:

* interpret CANON phases (SAFE / WARNING / BLACKHOLE)
* visualize informational geometry
* simulate decision consequences
* specialize interpretations for specific domains
  (e.g. finance, policy, optimization)

SANDBOX modules may use:

* numerical computation
* simulation
* visualization
* heuristics

**None of these techniques are allowed inside CANON.**

---

## What SANDBOX Is Not

SANDBOX modules must **never**:

* redefine CANON concepts
* introduce new decision classes
* override phase semantics
* weaken CANON guarantees
* claim formal correctness

SANDBOX has **no independent epistemic authority**.

---

## Relation to CANON

All SANDBOX guarantees derive exclusively from CANON.

For the formal statement of these guarantees, see:

`CANON_CONTRACT.md`

---

## SANDBOX Compliance Rule

Every SANDBOX module must satisfy the following rule:

> A sandbox result is valid **if and only if**
> it can be interpreted as a realization of a
> CANON-guaranteed decision.

In particular:

* SANDBOX may *interpret* CANON outcomes
* SANDBOX may *visualize* CANON phases
* SANDBOX may *apply* CANON decisions

But SANDBOX may never:

* invent new decision classes
* override phase semantics
* weaken CANON guarantees

This rule is non-negotiable.

---

## Status

* CANON: **stable / formally verified**
* SANDBOX: **experimental / exploratory**
* ENGINE: **external / downstream**

This separation is intentional and structural.

---

## Authorship and Scope

Author: Vincenzo Loventre
Formal core: Coq 8.18
SANDBOX scope: applied mathematics / interpretation / experimentation

SANDBOX exists to **extend the reach** of CANON
without ever compromising its integrity.

