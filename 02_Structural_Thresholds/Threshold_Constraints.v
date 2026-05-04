(******************************************************************************)
(*                                                                            *)
(*  Threshold_Constraints.v                                                   *)
(*                                                                            *)
(*  Structural constraints between thresholds                                 *)
(*                                                                            *)
(*  No numerics, no ordering on R, no metrics.                                 *)
(*  Only logical incompatibilities and necessity relations.                   *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Logic.

Require Import Structural_Core.LMetrics_Base.
Require Import Structural_Thresholds.Thresholds_Abstract.

(******************************************************************************)
(*  Fundamental non-collapse constraints                                       *)
(******************************************************************************)

(* No structure can be simultaneously stable and critical *)
Axiom Stable_not_Critical :
  forall L : LMetrics,
    Above_Stable_Threshold L ->
    ~ Below_Critical_Threshold L.

(* No structure can be simultaneously critical and isolating *)
Axiom Critical_not_Isolating :
  forall L : LMetrics,
    Below_Critical_Threshold L ->
    ~ Below_Isolating_Threshold L.

(******************************************************************************)
(*  Derived structural impossibilities                                         *)
(******************************************************************************)

Lemma Stable_excludes_Critical :
  forall L : LMetrics,
    Above_Stable_Threshold L ->
    ~ Below_Critical_Threshold L.
Proof.
  intros L Hs.
  apply Stable_not_Critical; assumption.
Qed.

Lemma Critical_excludes_Isolating :
  forall L : LMetrics,
    Below_Critical_Threshold L ->
    ~ Below_Isolating_Threshold L.
Proof.
  intros L Hc.
  apply Critical_not_Isolating; assumption.
Qed.

Lemma No_dual_membership :
  forall L : LMetrics,
    ~ (Above_Stable_Threshold L /\ Below_Critical_Threshold L).
Proof.
  intros L [Hs Hc].
  apply (Stable_excludes_Critical L Hs Hc).
Qed.

Lemma No_critical_isolating_overlap :
  forall L : LMetrics,
    ~ (Below_Critical_Threshold L /\ Below_Isolating_Threshold L).
Proof.
  intros L [Hc Hi].
  apply (Critical_excludes_Isolating L Hc Hi).
Qed.

(******************************************************************************)
(*  Global consistency of threshold partition                                  *)
(******************************************************************************)

Theorem Thresholds_consistent :
  forall L : LMetrics,
    ~ (Above_Stable_Threshold L
       /\ Below_Critical_Threshold L
       /\ Below_Isolating_Threshold L).
Proof.
  intros L [Hs [Hc Hi]].
  apply (Stable_excludes_Critical L Hs Hc).
Qed.

(******************************************************************************)
(*  End of file                                                               *)
(******************************************************************************)

