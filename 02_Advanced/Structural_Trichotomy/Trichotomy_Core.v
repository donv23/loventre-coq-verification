(*
  Trichotomy_Core.v

  Structural trichotomy core (Cycle 10, Chapter 26).

  This file introduces:
  - configurations
  - structural regimes
  - a minimal trichotomy axiom

  No dynamics, no metrics, no computation.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ===================================================== *)
(* === Primitive objects                               === *)
(* ===================================================== *)

Parameter Config : Type.

(* Structural regimes *)
Parameter Stable : Config -> Prop.
Parameter Critical : Config -> Prop.
Parameter Isolating : Config -> Prop.

(* ===================================================== *)
(* === Trichotomy axiom                                === *)
(* ===================================================== *)

(*
  Every configuration belongs to exactly one regime.
*)
Axiom structural_trichotomy :
  forall x : Config,
    (Stable x \/ Critical x \/ Isolating x)
    /\ ~ (Stable x /\ Critical x)
    /\ ~ (Stable x /\ Isolating x)
    /\ ~ (Critical x /\ Isolating x).

(*
  Epistemic status:
  - structural_trichotomy is a declared axiom.
  - Its non-eludibility will be explored in Trichotomy_Theorems.v.
*)

