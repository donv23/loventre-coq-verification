# Loventre — Coq Formalization (Verification Snapshot)

This repository contains a **Coq formalization** of the *Loventre model*,
provided **exclusively for independent verification**.

## Scope (Very Important)

- All statements and separations are **internal to the Loventre model**.
- This repository **does not** claim or imply a proof of the classical *P vs NP* problem.
- The purpose is **auditability**: reviewers can compile and check the scripts.

## Non-Goals

- This is **not** a collaborative development.
- Pull requests and extensions are **not solicited**.
- This repository is meant to be treated as a **read-only audit artifact**.

## Build

Tested with:
- Coq Platform 8.18

Verify (canonical smoke check):
```bash
make -f Makefile_SMOKE_ONLY verify

