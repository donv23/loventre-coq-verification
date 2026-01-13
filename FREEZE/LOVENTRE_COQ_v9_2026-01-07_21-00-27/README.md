## Formal verification (Coq)

This repository contains a minimal formal core of the Loventre model,
expressed in Coq.

### Axioms

The semantic assumptions of the model are explicitly documented in:

- `axioms/LOVENTRE_AXIOMS_v3_SEED_2025-12.md`

These axioms describe the geometric and informational structure
used by the formalization.

### Coq core

The file:

- `src/Loventre_Geometric_Separation.v`

contains the minimal axiomatic formalization of the geometric
P-like / NP-like separation internal to the Loventre model.

The presence of `Admitted` marks **explicit semantic assumptions**
(e.g. physical energy limits), not missing technical proofs.

### How to verify

```bash
cd src
coqc Loventre_Geometric_Separation.v

