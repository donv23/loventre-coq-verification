(*
  Exclusivity_Core.v
  LAB-11.1: Exhaustivity alone does NOT force uniqueness.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record RegimeStructure : Type := {
  Cfg : Type;
  Stable : Cfg -> Prop;
  Critical : Cfg -> Prop;
  Isolating : Cfg -> Prop;
  exhaustive_regimes : forall x : Cfg, Stable x \/ Critical x \/ Isolating x
}.

Definition Exclusive (S : RegimeStructure) : Prop :=
  (forall x : S.(Cfg), ~ (S.(Stable) x /\ S.(Critical) x)) /\
  (forall x : S.(Cfg), ~ (S.(Stable) x /\ S.(Isolating) x)) /\
  (forall x : S.(Cfg), ~ (S.(Critical) x /\ S.(Isolating) x)).

