(******************************************************************************)
(*                                                                            *)
(*  Structural_Invariants_Abstract.v                                          *)
(*                                                                            *)
(*  Abstract structural invariants over LMetrics                              *)
(*                                                                            *)
(*  No dynamics, no thresholds, no flow.                                      *)
(*  Only invariant structural predicates.                                    *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Logic.

Require Import Structural_Core.LMetrics_Base.

(******************************************************************************)
(*  Abstract structural invariants                                             *)
(******************************************************************************)

(* Generic invariant predicate *)
Parameter Invariant : (LMetrics -> Prop) -> Prop.

(******************************************************************************)
(*  Canonical structural invariants                                            *)
(******************************************************************************)

(* Stability is invariant *)
Axiom Stable_invariant :
  Invariant Stable.

(* Isolation is invariant *)
Axiom Isolating_invariant :
  Invariant Isolating.

(******************************************************************************)
(*  Invariants are mutually exclusive                                         *)
(******************************************************************************)

Axiom Stable_not_Isolating :
  forall L : LMetrics,
    Stable L -> ~ Isolating L.

Axiom Isolating_not_Stable :
  forall L : LMetrics,
    Isolating L -> ~ Stable L.

(******************************************************************************)
(*  Structural classification axiom                                           *)
(******************************************************************************)

Axiom Structural_trichotomy :
  forall L : LMetrics,
    Stable L \/ Isolating L \/ Critical L.

(******************************************************************************)
(*  End of file                                                               *)
(******************************************************************************)

