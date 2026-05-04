# Coq Setup and Verification Instructions

This repository contains a **minimal formal core** of the Loventre model,
implemented in Coq.

The code is intended to be **readable, auditable, and reproducible**.

---

## Required Software

- **Coq** ≥ 8.18  
  (tested with Coq Platform 8.18 on macOS)

---

## Compilation

From the repository root:

```bash
cd src
coqc Loventre_Geometric_Separation.v
coqc Loventre_Geometric_Separation_Corollary.v

