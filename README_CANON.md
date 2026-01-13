# LOVENTRE — CANON Mathematical Package

## Overview

This repository contains the **CANON core** of the Loventre theory,
a formally verified mathematical framework connecting:

- informational geometry
- phase semantics
- logical (non-computational) decision theory

All guarantees in this package are **proved in Coq**.

No heuristic, numerical tuning, or algorithmic assumption
is used at the CANON level.

---

## What CANON is

CANON is the **minimal stable mathematical nucleus** of the Loventre theory.

It provides:

1. A formal type of informational states (`LMetrics`)
2. A **total phase semantics**:
   - SAFE
   - WARNING
   - BLACKHOLE
3. A **logical decision relation**:
   - decisions exist
   - decisions are coherent
   - decisions are not functions or algorithms

Formally:
> for every valid informational state,  
> a coherent decision exists in the model.

---

## What CANON is NOT

CANON is **not**:

- a computational algorithm
- a classifier trained on data
- a heuristic scoring system
- a simulation or optimization loop

CANON does **not** choose.
It **guarantees existence and coherence**.

---

## Phase vs Decision

The model separates two levels:

### Phase (Geometry)
Defined by predicates on `LMetrics`:
- `is_SAFE`
- `is_WARNING`
- `is_BLACKHOLE`

Proved total and non-contradictory.

### Decision (Logic)
Defined by a relation:

