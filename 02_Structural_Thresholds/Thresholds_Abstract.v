(******************************************************************************)
(*                                                                            *)
(*  Thresholds_Abstract.v                                                     *)
(*                                                                            *)
(*  Abstract structural thresholds over LMetrics                              *)
(*                                                                            *)
(*  No numerics, no optimization, no computation.                             *)
(*  Only order, separation, and structural constraints.                      *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Logic.

Require Import Structural_Core.LMetrics_Base.
Require Import Structural_Core.Structural_Invariants_Abstract.

(******************************************************************************)
(*  Abstract threshold parameters                                              *)
(******************************************************************************)

(* Structural compatibility parameter *)
Parameter Theta : LMetrics -> Prop.

(* Canonical threshold predicates *)
Parameter Above_Stable_Threshold   : LMetrics -> Prop.
Parameter Below_Critical_Threshold : LMetrics -> Prop.
Parameter Below_Isolating_Threshold : LMetrics -> Prop.

(******************************************************************************)
(*  Minimal structural relations between thresholds                            *)
(******************************************************************************)

(* Stable region implies not isolating *)
Axiom Stable_not_Isolating :
  forall L : LMetrics,
    Above_Stable_Threshold L ->
    ~ Below_Isolating_Threshold L.

(* Isolating region excludes stability *)
Axiom Isolating_excludes_Stable :
  forall L : LMetrics,
    Below_Isolating_Threshold L ->
    ~ Above_Stable_Threshold L.

(* Critical region lies strictly between *)
Axiom Critical_between :
  forall L : LMetrics,
    ~ Above_Stable_Threshold L ->
    ~ Below_Isolating_Threshold L ->
    Below_Critical_Threshold L.

(******************************************************************************)
(*  Structural separation lemmas                                               *)
(******************************************************************************)

Lemma Stable_and_Isolating_contradiction :
  forall L : LMetrics,
    Above_Stable_Threshold L ->
    Below_Isolating_Threshold L ->
    False.
Proof.
  intros L Hs Hi.
  apply (Stable_not_Isolating L); assumption.
Qed.

Lemma No_triple_overlap :
  forall L : LMetrics,
    ~ (Above_Stable_Threshold L
       /\ Below_Critical_Threshold L
       /\ Below_Isolating_Threshold L).
Proof.
  intros L [Hs [Hc Hi]].
  apply (Stable_and_Isolating_contradiction L Hs Hi).
Qed.

(******************************************************************************)
(*  End of file                                                               *)
(******************************************************************************)

