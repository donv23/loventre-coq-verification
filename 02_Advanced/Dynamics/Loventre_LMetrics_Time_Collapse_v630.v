(**
   Loventre_LMetrics_Time_Collapse_v630.v
   --------------------------------------
   Primo tentativo di definire un "tempo di collasso"
   nel modello dinamico.
*)

From Stdlib Require Import Nat PeanoNat Bool.
From Loventre_Core Require Import
     Loventre_Core_Prelude
     Loventre_Kernel
     Loventre_Foundation_Types
     Loventre_Foundation_Params
     Loventre_Foundation_Entropy.

From Loventre_Advanced Require Import
     Loventre_LMetrics_Core
     Loventre_Metrics_Bus
     Loventre_Class_Model
     Loventre_Class_Properties.

From Loventre_Advanced.Dynamics Require Import
     Loventre_LMetrics_Time_Model_v600
     Loventre_LMetrics_Time_From_JSON_v610
     Loventre_LMetrics_Time_EvolveN_v620.

Set Primitive Projections.

(**
   A. Predicato blackhole booleano dal record LMetrics
*)

Definition is_blackhole (m : LMetrics) : bool :=
  match classify_instance m with
  | NP_like_blackhole => true
  | _ => false
  end.

(**
   B. Cerca un punto n <= limit in cui evolve_n atterra in NP_bh.
*)

Fixpoint collapse_time_bounded (limit : nat) (m0 : LMetrics) : option nat :=
  match limit with
  | O =>
      if is_blackhole m0 then Some 0 else None
  | S limit' =>
      let mn := metrics_after_n_steps limit m0 in
      if is_blackhole mn
      then Some limit
      else collapse_time_bounded limit' m0
  end.

(**
   C. Proprietà base: se è già blackhole, tempo = 0
*)

Lemma collapse_time_zero :
  forall m,
    is_blackhole m = true ->
    collapse_time_bounded 0 m = Some 0.
Proof.
  intros m H. simpl. rewrite H. reflexivity.
Qed.

(**
   D. Se limit non basta, risultato None
*)

Lemma collapse_time_none_if_never :
  forall L m,
    (forall n, n <= L -> is_blackhole (metrics_after_n_steps n m) = false) ->
    collapse_time_bounded L m = None.
Proof.
  induction L as [|L IH]; intros m Hnever.
  - simpl. specialize (Hnever 0 (Nat.le_0_l 0)).
    rewrite Hnever. reflexivity.
  - simpl.
    specialize (Hnever (S L) (Nat.le_succ_diag_r L)).
    rewrite Hnever. apply IH.
    intros n Hn. apply Hnever.
Qed.

