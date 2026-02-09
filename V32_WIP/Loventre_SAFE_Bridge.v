From Stdlib Require Import String.

Require Import Loventre_Witness_Loader.
Require Import Loventre_SAFE_Predicate.

(* ==================================================== *)
(* Parser string -> LClass                              *)
(* ==================================================== *)
Definition parse_LClass (s : string) : LClass :=
  if String.eqb s "P_STR" then P_STR
  else if String.eqb s "P_ACC" then P_ACC
  else BH_NP.

(* ==================================================== *)
(* Derive SAFE from the witness                         *)
(* ==================================================== *)

Lemma Loventre_Witness_is_SAFE :
  Loventre_SAFE (parse_LClass LoventreWitness_Instance.(w_lmetrics_type)).
Proof.
  unfold LoventreWitness_Instance.
  simpl.

  (* Match on parsed semantic class *)
  destruct (String.eqb "P_STR" "P_STR") eqn:HS1.
  - apply Safe_PSTR.
  - discriminate.
Qed.

