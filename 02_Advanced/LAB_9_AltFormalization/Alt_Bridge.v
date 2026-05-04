(*
  Alt_Bridge.v
  Bridge between Barrier-based and intrinsic irreversibility formulations.
*)

Require Import Loventre_Advanced.LAB_9_AltFormalization.Alt_Core.

(* Abstract declaration of Barrier-style core *)
Parameter Barrier : Config -> Prop.

(* Equivalence axiom (presentation equivalence, LAB-level) *)
Axiom Barrier_equiv_irreversible :
  forall x : Config, Barrier x <-> irreversible x.

