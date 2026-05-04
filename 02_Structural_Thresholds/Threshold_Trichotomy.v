(******************************************************************************)
(*                                                                            *)
(*  Threshold_Trichotomy.v                                                    *)
(*                                                                            *)
(*  Structural trichotomy induced by abstract thresholds                      *)
(*                                                                            *)
(*  Purely propositional: no numerics, no ordering on values.                 *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Logic.

Require Import Structural_Core.LMetrics_Base.
Require Import Structural_Thresholds.Thresholds_Abstract.

(******************************************************************************)
(*  Structural trichotomy axiom                                               *)
(******************************************************************************)

Axiom Threshold_trichotomy :
  forall L : LMetrics,
    Above_Stable_Threshold L
    \/ Below_Critical_Threshold L
    \/ Below_Isolating_Threshold L.

(******************************************************************************)
(*  Derived exclusion properties                                              *)
(******************************************************************************)

Lemma Stable_excludes_Isolating :
  forall L : LMetrics,
    Above_Stable_Threshold L ->
    ~ Below_Isolating_Threshold L.
Proof.
  intros L Hs.
  apply Stable_not_Isolating with (L := L).
  exact Hs.
Qed.

Lemma Isolating_excludes_Stable :
  forall L : LMetrics,
    Below_Isolating_Threshold L ->
    ~ Above_Stable_Threshold L.
Proof.
  intros L Hi.
  apply Isolating_excludes_Stable with (L := L).
  exact Hi.
Qed.

(******************************************************************************)
(*  Structural classification theorem                                         *)
(******************************************************************************)

Theorem Structural_threshold_classification :
  forall L : LMetrics,
    Above_Stable_Threshold L
 \/ Below_Critical_Threshold L
 \/ Below_Isolating_Threshold L.
Proof.
  intro L.
  apply Threshold_trichotomy.
Qed.

(******************************************************************************)
(*  End of file                                                               *)
(******************************************************************************)

