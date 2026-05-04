(*
  CounterModel_Overlap.v
  LAB-11.1: A structure can be exhaustive but not exclusive.
*)

Require Import Loventre_Advanced.LAB_11_Axiom_Breaking.L11_1_Exclusivity.Exclusivity_Core.

Inductive One : Type := p.

Definition StableM (_ : One) : Prop := True.
Definition CriticalM (_ : One) : Prop := True.
Definition IsolatingM (_ : One) : Prop := True.

Lemma exhaustiveM : forall x : One, StableM x \/ CriticalM x \/ IsolatingM x.
Proof.
  intro x; left; exact I.
Qed.

Definition S : RegimeStructure :=
  {| Cfg := One;
     Stable := StableM;
     Critical := CriticalM;
     Isolating := IsolatingM;
     exhaustive_regimes := exhaustiveM |}.

Lemma not_exclusive : ~ Exclusive S.
Proof.
  intro Hex.
  destruct Hex as [Hsc [Hsi Hci]].
  specialize (Hsc p).
  apply Hsc.
  split; exact I.
Qed.

