# Axis C — Conceptual Map
## Loventre Model ↔ Classical Complexity

**Status:** AXIS C (Interpretative / Non-Canonical)  
**Scope:** Conceptual alignment only  
**Affects CANON:** NO  

---

## 1. Purpose of Axis C

Axis C exists to **interpret** the Loventre complexity model
in relation to classical notions (P, NP, NP-hard),
**without claiming** any classical separation such as P ≠ NP.

Axis C:
- does not add axioms to the CANON
- does not modify verified Coq developments
- does not attempt classical reductions or completeness proofs

It is a **semantic bridge**, not a proof layer.

---

## 2. Loventre Internal Classes (Model-Specific)

Within the Loventre model, problems are classified as:

| Loventre Class | Informal Meaning |
|---------------|------------------|
| **P_STR** | Strongly polynomial / stable |
| **P_ACC** | Polynomial but fragile / accessible |
| **BH_NP** | Black-hole-like, informationally opaque |

These classes are **internal to the Loventre framework** and
are not claimed to coincide with classical complexity classes.

---

## 3. Classical Vocabulary (Axis C Only)

Axis C introduces minimal classical notions:

- **Problem**
- **In_P**
- **In_NP**
- **NP_hard**
- **NP_complete**
- **Polynomial reduction**

These are introduced **abstractly**, without computational content.

---

## 4. Interpretative Alignment (Non-Equivalence)

The following table represents an **interpretative alignment**,
not a formal equivalence:

| Classical Notion | Loventre Interpretation |
|------------------|------------------------|
| P (easy problems) | Often fall into **P_STR** |
| NP (verifiable) | May fall into **P_ACC** |
| NP-hard / NP-complete | Candidates for **BH_NP** |

⚠️ This alignment is:
- heuristic
- model-dependent
- non-bijective
- non-assertive

No implication is claimed in the reverse direction.

---

## 5. What Axis C Explicitly Does NOT Claim

Axis C does **NOT** claim:

- P ≠ NP
- NP-hard ⊄ P
- any classical separation theorem
- any reduction-based impossibility result

All statements involving classical complexity
remain **conditional** and **interpretative**.

---

## 6. Role of the Python Engine

The Python Loventre Engine:
- explores empirical behavior of the Loventre model
- supports intuition and diagnostics
- is **not** a proof engine
- is **not** part of the public verification

It does not establish classical results.

---

## 7. Safety and IP Considerations

Axis C is designed to:
- preserve patentability
- avoid public disclosure of the engine
- separate theory from implementation
- maintain a clean verification boundary

The CANON Coq v3 remains the **only formal source of validity**.

---

## 8. Next Possible Steps

From this conceptual map, one may:

- write **conditional lemmas** (Axis C / Coq)
- prepare explanatory material for reviewers
- stop at this level and freeze Axis C

Any further step must preserve the interpretative nature of Axis C.

