From Stdlib Require Import String.
Open Scope string_scope.

Require Import Loventre_Witness_Loader.
Require Import Loventre_SAFE_Predicate.

(* =================================================== *)
(*  Canvas 36 — Witness SAFE Global                    *)
(* =================================================== *)

(* Witness type proof *)
Lemma Witness_type_is_PSTR :
  LoventreWitness_Instance.(w_lmetrics_type) = "P_STR"%string.
Proof. reflexivity. Qed.

(* Convert string to LClass *)
Definition decode_lclass (s:string) : LClass :=
  if string_dec s "P_STR"%string then P_STR
  else if string_dec s "P_ACC"%string then P_ACC
  else BH_NP.

(* The LClass of our witness *)
Definition Witness_LClass : LClass :=
  decode_lclass LoventreWitness_Instance.(w_lmetrics_type).

(* The SAFE lemma *)
Lemma Witness_is_SAFE : Loventre_SAFE Witness_LClass.
Proof.
  unfold Witness_LClass.
  rewrite Witness_type_is_PSTR.
  simpl.
  apply Safe_PSTR.
Qed.

