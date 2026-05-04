(*
  CounterModel_Tricho.v
  LAB-A2: Model with unclassified configurations.
*)

Require Import Loventre_Advanced.LAB_A_Independence.A2_NoTrichotomy.Core_NoTrichotomy.

Inductive Cfg : Type := x.

Definition StableM (_:Cfg) : Prop := False.
Definition CriticalM (_:Cfg) : Prop := False.
Definition IsolatingM (_:Cfg) : Prop := False.

Lemma exists_unclassified :
  exists c : Cfg, ~ StableM c /\ ~ CriticalM c /\ ~ IsolatingM c.
Proof.
  exists x; repeat split; intro H; exact H.
Qed.

