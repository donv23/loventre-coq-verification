(**
  Loventre_LMetrics_Perturbation.v
  dicembre 2025

  Layer dinamico — perturbazioni e invarianza debole.

  Questo file NON dimostra nulla.
  Introduce solo definizioni astratte.
*)

From Stdlib Require Import Reals.
Local Open Scope R_scope.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_LMetrics_Robustness.

Module LMetrics_Perturbation.

  Import Loventre_LMetrics.
  Import LMetrics_Robustness.

  (**
    Perturbazione astratta su LMetrics.
  *)
  Parameter perturb : LMetrics -> LMetrics.

  (**
    Perturbazione ammessa (placeholder).
  *)
  Definition is_admissible_perturbation : Prop := True.

  (**
    Invarianza debole sotto perturbazione.

    Una metrica è debolmente invariante se:
    - è canonicamente robusta
    - la sua perturbazione resta canonicamente robusta

    Nessuna ipotesi su *come* o *perché*.
  *)
  Definition is_weakly_invariant_under_perturbation (M : LMetrics) : Prop :=
    is_canonical_robust M ->
    is_canonical_robust (perturb M).

End LMetrics_Perturbation.

