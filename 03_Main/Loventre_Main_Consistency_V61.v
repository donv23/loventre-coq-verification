(** Loventre_Main_Consistency_V61.v
    Coerenza minima delle tre classi Loventre (V61-03)
 *)

From Stdlib Require Import Bool.

From Loventre_Main Require Import
  Loventre_Main_Prelude
  Loventre_Main_Predicates
  Loventre_Main_Classes
  Loventre_Main_Theorem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Se m è P_like, m non è blackhole-like *)
Lemma Consistency_P_like_not_BH : forall m,
  In_P_like m -> ~ In_NP_blackhole_like m.
Proof.
  intros m Hp.
  unfold In_NP_blackhole_like, In_P_like in *.
  eapply SAFE_not_BlackHole; eauto.
Qed.

(** Nessun modello può appartenere simultaneamente
    a P_accessible_like e NP_blackhole_like *)
Lemma Consistency_Pacc_vs_BH : forall m,
  In_P_accessible_like m -> ~ In_NP_blackhole_like m.
Proof.
  intros m [Hsafe _].
  unfold In_P_like, In_P_accessible_like in *.
  eapply SAFE_not_BlackHole; eauto.
Qed.

(** Se un witness è NP_blackhole_like, non è SAFE *)
Lemma Consistency_BH_not_P : forall m,
  In_NP_blackhole_like m -> ~ In_P_like m.
Proof.
  intros m Hbh Hp.
  unfold In_NP_blackhole_like, In_P_like in *.
  eapply SAFE_not_BlackHole; eauto.
Qed.

(** Conclusione meta: classi non collassano a P *)
Theorem Loventre_Class_Separation_Minimal :
  exists m,
      In_NP_blackhole_like m
   /\ ~ In_P_like m.
Proof.
  (** testimone critico dal Main_Theorem *)
  apply Exist_Critical_Witness.
Qed.

