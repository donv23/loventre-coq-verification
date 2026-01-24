(* ******************************************************************* *)
(*  Loventre_Mini_Theorem_v2.v – nucleo dimostrativo coerente          *)
(* ******************************************************************* *)

From Coq Require Import Init.Logic.

From Loventre_Geometry Require Import
  Loventre_LMetrics_JSON_Witness
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_Accessible_Existence.

(* ------------------------------------------------------------------ *)
(*  Tripla esistenza P / P_accessible / NP_like-black-hole            *)
(* ------------------------------------------------------------------ *)

Definition Loventre_triple_exist : Prop :=
  (exists mP : LMetrics, is_P_like mP)
  /\
  (exists mPacc : LMetrics, is_P_like_accessible mPacc)
  /\
  (exists mNP : LMetrics, is_NP_like_black_hole mNP).

(* ------------------------------------------------------------------ *)
(*  Teorema Mini V2                                                   *)
(* ------------------------------------------------------------------ *)

Theorem Loventre_triple_exist_true :
  Loventre_triple_exist.
Proof.
  unfold Loventre_triple_exist.
  destruct Loventre_P_vs_NP_like_black_hole_exist_predicative as [HP HNP].
  destruct exists_P_like_accessible as [mPacc HPacc].
  repeat split.
  - exact HP.
  - exists mPacc. exact HPacc.
  - exact HNP.
Qed.

(* ------------------------------------------------------------------ *)
(*  Dummy lemma per stand-by e stabilità di compilazione              *)
(* ------------------------------------------------------------------ *)

Lemma Loventre_Mini_V2_standalone_true : True.
Proof. exact I. Qed.

(* ******************************************************************* *)
(*  EOF                                                                *)
(* ******************************************************************* *)

