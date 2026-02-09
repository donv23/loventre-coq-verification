From Stdlib Require Import String.

(* ==================================================== *)
(* LOVENTRE SAFE PREDICATE (Canvas 33)                  *)
(* ==================================================== *)

Inductive LClass : Type :=
| P_STR
| P_ACC
| BH_NP.

(* SAFE means: not black-hole NP *)
Inductive Loventre_SAFE : LClass -> Prop :=
| Safe_PSTR : Loventre_SAFE P_STR
| Safe_PACC : Loventre_SAFE P_ACC.

(* BH_NP is NOT SAFE automatically *)
Lemma BHNP_not_SAFE : Loventre_SAFE BH_NP -> False.
Proof.
intro H.
inversion H.
Qed.

(* convenience lemma: not SAFE iff BH_NP *)
Lemma BHNP_exact_notSAFE : ~ Loventre_SAFE BH_NP.
Proof.
intros H.
inversion H.
Qed.

