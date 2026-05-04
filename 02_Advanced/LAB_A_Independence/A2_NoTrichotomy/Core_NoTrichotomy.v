(*
  Core_NoTrichotomy.v
  LAB-A2: Core WITHOUT trichotomy exhaustivity.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Parameter Config : Type.
Parameter Stable Critical Isolating : Config -> Prop.

(* Mutual exclusion kept *)
Axiom no_SC : forall x : Config, ~(Stable x /\ Critical x).
Axiom no_SI : forall x : Config, ~(Stable x /\ Isolating x).
Axiom no_CI : forall x : Config, ~(Critical x /\ Isolating x).

(* NOTE: exhaustivity REMOVED *)

