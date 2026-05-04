(******************************************************************************)
(*                                                                            *)
(*  Structural_Dynamics_Invariants.v                                          *)
(*                                                                            *)
(*  Interaction between structural dynamics and structural invariants         *)
(*                                                                            *)
(*  No thresholds, no parameters, no classification.                          *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Logic.

Require Import Structural_Core.LMetrics_Base.
Require Import Structural_Core.Structural_Invariants_Abstract.
Require Import Structural_Core.Structural_Dynamics_Abstract.

(******************************************************************************)
(*  Invariants preserved by structural flow                                   *)
(******************************************************************************)

Axiom Flow_preserves_invariants :
  forall (P : LMetrics -> Prop),
    Invariant P ->
    forall (L1 L2 : LMetrics),
      L1 ~~> L2 ->
      P L1 ->
      P L2.

(******************************************************************************)
(*  Canonical preservation lemmas                                              *)
(******************************************************************************)

Lemma Flow_preserves_Stable :
  forall (L1 L2 : LMetrics),
    Stable L1 ->
    L1 ~~> L2 ->
    Stable L2.
Proof.
  intros L1 L2 Hstable Hflow.
  eapply (Flow_preserves_invariants Stable).
  - exact Stable_invariant.
  - exact Hflow.
  - exact Hstable.
Qed.

Lemma Flow_preserves_Isolating :
  forall (L1 L2 : LMetrics),
    Isolating L1 ->
    L1 ~~> L2 ->
    Isolating L2.
Proof.
  intros L1 L2 Hisol Hflow.
  eapply (Flow_preserves_invariants Isolating).
  - exact Isolating_invariant.
  - exact Hflow.
  - exact Hisol.
Qed.

(******************************************************************************)
(*  End of file                                                               *)
(******************************************************************************)

