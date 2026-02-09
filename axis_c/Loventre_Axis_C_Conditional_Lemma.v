(* =============================================== *)
(* Axis C — Conditional Lemma (LAB)                 *)
(* =============================================== *)

From Stdlib Require Import Logic.

Require Import Axis_C.Loventre_Axis_C_Classical_Definitions.

(* ------------------------------------------------ *)
(* Lemma condizionale: nessun claim incondizionato  *)
(* ------------------------------------------------ *)

Lemma Axis_C_Conditional_Separability :
  Axis_C.Axis_C_Separability -> True.
Proof.
  intros _.
  exact I.
Qed.

