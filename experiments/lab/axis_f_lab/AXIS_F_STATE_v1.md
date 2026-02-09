---

## 8. Interaction with CANON JSON ↔ Coq Crosscheck

The Loventre engine includes a **CANON-level JSON ↔ Coq crosscheck**
whose purpose is to ensure consistency between:

- canonical witness JSON files
- canonical Coq witness definitions

Axis F deliberately introduces **additional JSON witnesses**
(e.g. 3-SAT instances) that are:

- LAB-only
- non-canonical
- not referenced in `Loventre_LMetrics_JSON_Link.v`

As a consequence:

- the CANON crosscheck may report these files as “extra”
- this behavior is **expected and correct**
- it does **not** indicate an error or inconsistency

No modification to the CANON crosscheck is permitted or required.

Axis F remains fully isolated and does not affect CANON validity.

