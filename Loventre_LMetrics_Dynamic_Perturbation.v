(**
  Loventre_LMetrics_Dynamic_Perturbation.v

  Dynamic Layer v0 — Skeleton only

  Purpose:
  Introduce an abstract notion of perturbation
  acting on LMetrics, without assuming any property.
*)

From Stdlib Require Import Reals.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_Global_Invariant_Stub.

Module Loventre_Dynamic_Perturbation.

  Import Loventre_LMetrics.
  Import Loventre_Global_Invariant.

  (**
    Abstract type of perturbations.

    No structure is assumed.
  *)
  Parameter Perturbation : Type.

  (**
    Application of a perturbation to LMetrics.
  *)
  Parameter apply_perturbation :
    Perturbation -> LMetrics -> LMetrics.

  (**
    Dynamic preservation predicate.

    This is NOT assumed to hold.
    It is only a well-formed question.
  *)
  Definition preserves_coherence
             (p : Perturbation) : Prop :=
    forall M : LMetrics,
      Globally_Coherent M ->
      Globally_Coherent (apply_perturbation p M).

End Loventre_Dynamic_Perturbation.

