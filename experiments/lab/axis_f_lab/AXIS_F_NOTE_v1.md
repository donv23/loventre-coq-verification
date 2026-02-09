# AXIS F — Explicit NP Distinctions (LAB)

**Author:** Vincenzo Loventre  
**Status:** LAB / Observational / Non-canonical  
**Last verified:** Engine + Theory GREEN  
**Scope:** Conceptual clarification only  

---

## 1. Purpose of Axis F

Axis F is an **exploratory laboratory axis** whose goal is to clarify
a fundamental ambiguity in classical complexity discussions:

> the implicit identification between *class membership* and
> *structural computational behavior*.

Axis F introduces **no new formal classes**, **no axioms**, and
**no claims**.  
It is strictly descriptive.

---

## 2. The Three Explicit Distinctions

Axis F makes explicit a **triple distinction** that already
*emerges naturally* from the Loventre Engine outputs.

### 2.1 NP-classical (class)

The **classical complexity classification** of a problem:
- P
- NP-complete
- unknown / not classified

This corresponds to standard textbook notions.

---

### 2.2 NP-instance-easy / hard (instance profile)

The **local difficulty profile of a specific instance**, independently
of its class:
- easy
- critical
- hard
- unknown

This is an *instance-level* notion and is **orthogonal** to class
membership.

---

### 2.3 NP-structural (regime)

The **structural computational regime** detected by the Loventre Engine:
- `P_like_like`
- `P_like_accessible`
- `NP_like_black_hole`

This notion is **purely structural** and refers to:
- curvature
- horizon formation
- irreversibility
- tunneling behavior

---

## 3. Key Observations from Axis F

The following facts are **observed**, not postulated.

### Observation A — NP-complete ≠ structural black hole

Some NP-complete instances fall in **P-like structural regimes**.

Example:
- NP-classical: NP-complete
- structural regime: `meta_P_like_like`

---

### Observation B — P-class ≠ instance easy

Some P-class problems admit **hard instances** without forming
black-hole regimes.

Example:
- NP-classical: P
- instance profile: hard
- structural regime: `P_like_accessible`

---

### Observation C — Black hole ≠ NP-classical (naïve sense)

The black-hole regime correlates with **structural features**,
not with nominal class membership alone.

---

## 4. Interpretation

Axis F suggests that the commonly used dichotomy:

> P vs NP

implicitly conflates **three distinct layers**:

1. class membership  
2. instance-level difficulty  
3. structural computational regime  

The Loventre framework naturally separates them.

---

## 5. What Axis F Does NOT Claim

Axis F does **not** claim:

- a proof of P ≠ NP
- a reduction-based separation
- a correspondence theorem with Turing machines
- a new complexity class
- any modification of the Loventre CANON

All interpretations beyond the descriptive level are **explicitly rejected**.

---

## 6. Relationship to Other Axes

- Axis A–D: canonical, frozen
- Axis E: formal internal separation (model-relative)
- **Axis F: observational clarification only**

Axis F is intentionally **kept outside the CANON**.

---

## 7. Verification

Axis F relies exclusively on:
- existing witness JSON files
- existing engine outputs

No engine modification is performed.

To reproduce observations:

```bash
python3 axis_f_classifier.py

