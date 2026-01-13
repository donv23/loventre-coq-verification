(** Loventre_Main_Theorem_V61_Chain.v
    Collegamento incrementale: V61 -> nucleo *)

From Loventre_Main Require Import
  Loventre_Main_Prelude
  Loventre_Main_Witness
  Loventre_Main_Predicates
  Loventre_Main_Classes.

From Loventre_Main Require Import
  Loventre_Main_Theorem_V61
  Loventre_Main_Theorem.

From Loventre_Advanced Require Import
  Loventre_LMetrics_Core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** --------------------------------------------------------------------- *)
(**  Chain lemma:
     Un risultato V61 relativamente forte implica
     una forma del teorema principale di base. *)

Lemma Loventre_Main_Theorem_V61_implies_Main :
  Loventre_Main_Theorem_V61 ->
  forall m, In_NP_blackhole_like m -> BlackHole m.
Proof.
  intros H m Hbh.
  unfold In_NP_blackhole_like in *.
  exact Hbh.
Qed.

(** Un alias più naturale, come corollario. *)

Corollary Loventre_Main_Theorem_V61_to_V55 :
  Loventre_Main_Theorem_V61 -> Loventre_Main_Theorem.
Proof.
  unfold Loventre_Main_Theorem.
  intros H m.
  specialize (Loventre_Main_Theorem_V61_implies_Main H m).
  tauto.
Qed.


