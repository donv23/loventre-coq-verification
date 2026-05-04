(*
  LAB-12.3 — Countermodel:
  three pairwise-exclusive regimes do NOT force triplet coverage
*)

Require Import
  Loventre_Advanced.LAB_12_Minimal_Rigidity.L12_3_Triplet.Core_Triplet.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Core_Triplet.

(* === Abstract configurations === *)

Parameter a b c : Config.

Axiom distinct_ab : a <> b.
Axiom distinct_bc : b <> c.
Axiom distinct_ac : a <> c.

(* === Regimes === *)

Axiom R1_a : R1 a.
Axiom R2_b : R2 b.

Axiom R1_only_a : forall x : Config, R1 x -> x = a.
Axiom R2_only_b : forall x : Config, R2 x -> x = b.
Axiom R3_empty  : forall x : Config, R3 x -> False.

(* === Pairwise exclusivity holds === *)

Lemma excl_12 : forall x : Config, ~(R1 x /\ R2 x).
Proof.
  intros x [H1 H2].
  apply R1_only_a in H1.
  apply R2_only_b in H2.
  apply distinct_ab.
  rewrite <- H1.
  exact H2.
Qed.

Lemma excl_13 : forall x : Config, ~(R1 x /\ R3 x).
Proof.
  intros x [_ H].
  apply R3_empty in H.
  exact H.
Qed.

Lemma excl_23 : forall x : Config, ~(R2 x /\ R3 x).
Proof.
  intros x [_ H].
  apply R3_empty in H.
  exact H.
Qed.

(* === Triplet coverage fails === *)

Lemma no_triplet_cover :
  ~ TripletCover.
Proof.
  unfold TripletCover.
  intro H.
  specialize (H c).
  destruct H as [Hc1 | [Hc2 | Hc3]].
  - apply R1_only_a in Hc1.
    apply distinct_ac.
    rewrite <- Hc1.
    reflexivity.
  - apply R2_only_b in Hc2.
    apply distinct_bc.
    rewrite <- Hc2.
    reflexivity.
  - apply R3_empty in Hc3.
    exact Hc3.
Qed.

