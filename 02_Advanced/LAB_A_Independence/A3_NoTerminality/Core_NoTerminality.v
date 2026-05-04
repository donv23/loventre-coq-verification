(*
  Core_NoTerminality.v
  LAB-A3: Core WITHOUT terminality of barriers.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Parameter Config : Type.
Parameter trans : Config -> Config -> Prop.
Parameter Barrier : Config -> Prop.

(* NOTE: terminality axiom REMOVED *)

