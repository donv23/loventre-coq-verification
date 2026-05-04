(******************************************************************************)
(*                                                                            *)
(*  LMetrics_Base.v                                                           *)
(*                                                                            *)
(*  Structural core: primitive objects and predicates                          *)
(*                                                                            *)
(*  This file introduces the minimal abstract structure of the theory.         *)
(*  No dynamics, no numerics, no interpretation.                               *)
(*                                                                            *)
(******************************************************************************)

From Coq Require Import PropExtensionality.

(******************************************************************************)
(*  Primitive type                                                            *)
(******************************************************************************)

(* Abstract type of structural metrics *)
Parameter LMetrics : Type.

(******************************************************************************)
(*  Structural predicates                                                     *)
(******************************************************************************)

(* Stable structural regime *)
Parameter Stable : LMetrics -> Prop.

(* Critical structural regime *)
Parameter Critical : LMetrics -> Prop.

(* Isolating / barrier-dominated structural regime *)
Parameter Isolating : LMetrics -> Prop.

(******************************************************************************)
(*  Structural sanity axioms (minimal)                                        *)
(******************************************************************************)

(* The three regimes are mutually exclusive *)
Axiom Stable_not_Critical :
  forall L : LMetrics, Stable L -> ~ Critical L.

Axiom Stable_not_Isolating :
  forall L : LMetrics, Stable L -> ~ Isolating L.

Axiom Critical_not_Isolating :
  forall L : LMetrics, Critical L -> ~ Isolating L.

(******************************************************************************)
(*  Structural completeness (trichotomy, abstract)                             *)
(******************************************************************************)

(* Every structural metric belongs to exactly one regime *)
Axiom Structural_Trichotomy :
  forall L : LMetrics,
    Stable L \/ Critical L \/ Isolating L.

(******************************************************************************)
(*  End of file                                                               *)
(******************************************************************************)

