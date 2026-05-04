(*
  LAB-15.1 — Core_SAFE_Region.v

  Definition of SAFE regions:
  regions that are internally rigid and closed under admissible paths.

  This is the operational notion of stability used later
  to characterize P-like behavior.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* === Abstract configuration space === *)

Parameter Config : Type.

(* === Transition relation === *)

Parameter trans : Config -> Config -> Prop.

(* === Path relation (abstract) === *)

Parameter path : Config -> Config -> Prop.

(* === Region predicate === *)

Parameter Region : Config -> Prop.

(* === Internal path: stays inside the region === *)

Definition internal_path (x y : Config) : Prop :=
  path x y /\ Region x /\ Region y.

(* === Internal rigidity === *)

Definition InternallyRigid : Prop :=
  forall x y : Config,
    internal_path x y -> ~ internal_path y x.

(* === Closure under paths === *)

Definition PathClosed : Prop :=
  forall x y : Config,
    Region x -> path x y -> Region y.

(* === SAFE region === *)

Definition SAFE : Prop :=
  InternallyRigid /\ PathClosed.

