(* ============================================================= *)
(* LAB19_1_Toy_BlackHole.v                                       *)
(*                                                              *)
(* Toy Coq minimale per LAB-19.1                                *)
(*                                                              *)
(* Scopo: fornire un witness formale, isolato e minimale        *)
(* di NP-like-black-hole come inaccessibilità globale            *)
(* strutturalmente stabile.                                     *)
(*                                                              *)
(* VINCOLI RISPETTATI:                                          *)
(* - nessun Metrics Bus                                         *)
(* - nessun SAFE                                                *)
(* - nessun P-like / NP-like preesistenti                        *)
(* - nessuna dinamica, path o rigidità                           *)
(* - isolamento completo dal canone                             *)
(* ============================================================= *)

From Stdlib Require Import Logic.

(* ------------------------------------------------------------- *)
(* Core minimale                                                  *)
(* ------------------------------------------------------------- *)

Parameter Config : Type.

(* Canale globale astratto *)
Parameter global_channel : Config -> Prop.

(* ------------------------------------------------------------- *)
(* Accessibilità globale                                         *)
(* ------------------------------------------------------------- *)

Definition globally_accessible (c : Config) : Prop :=
  global_channel c.

(* ------------------------------------------------------------- *)
(* Black hole (definizione negativa)                             *)
(* ------------------------------------------------------------- *)

Definition black_hole (c : Config) : Prop :=
  ~ globally_accessible c.

(* ------------------------------------------------------------- *)
(* Trasformazioni locali (astratte)                              *)
(* ------------------------------------------------------------- *)

Parameter local_transform : Config -> Config.

(* ------------------------------------------------------------- *)
(* Stabilità strutturale                                        *)
(* ------------------------------------------------------------- *)

Definition stable_black_hole (c : Config) : Prop :=
  black_hole c /\
  black_hole (local_transform c).

(* ------------------------------------------------------------- *)
(* Witness minimale                                              *)
(* ------------------------------------------------------------- *)

Parameter bh : Config.

Axiom bh_is_stable_black_hole :
  stable_black_hole bh.

(* ------------------------------------------------------------- *)
(* Lemmi di controllo (audit)                                   *)
(* ------------------------------------------------------------- *)

Lemma bh_not_globally_accessible :
  ~ globally_accessible bh.
Proof.
  pose proof bh_is_stable_black_hole as H.
  unfold stable_black_hole, black_hole in H.
  destruct H as [H _].
  exact H.
Qed.

Lemma bh_transform_not_globally_accessible :
  ~ globally_accessible (local_transform bh).
Proof.
  pose proof bh_is_stable_black_hole as H.
  unfold stable_black_hole, black_hole in H.
  destruct H as [_ H].
  exact H.
Qed.

Lemma LAB19_1_toy_ok : True.
Proof. exact I. Qed.

(* ============================================================= *)
(* END OF FILE                                                   *)
(* ============================================================= *)

