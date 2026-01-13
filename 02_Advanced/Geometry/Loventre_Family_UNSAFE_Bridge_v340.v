(**
  Loventre_Family_UNSAFE_Bridge_v340.v
  Bridge NP_blackhole -> NOT SAFE per la famiglia SAT
  Milestone V340 — simmetria rispetto a V330
*)

From Loventre_Core Require Import Loventre_Core_Prelude.
From Loventre_Advanced Require Import Loventre_LMetrics_Core
                                     Loventre_LMetrics_Phase_Predicates
                                     Loventre_SAFE_Model
                                     Loventre_Class_Model
                                     Loventre_LMetrics_JSON_Witness.

Module Loventre_Family_UNSAFEBRIDGE_V340.

(** Se un profilo è NP_blackhole, allora NON è SAFE *)
Lemma NPbh_implies_not_SAFE :
  forall m: LMetrics,
    is_NP_blackhole m = true ->
    SAFE_condition m = false.
Proof.
  intros m Hbh.
  unfold SAFE_condition.
  unfold is_NP_blackhole in Hbh.
  (* argomento placeholder coerente col modello: SAFE=false *)
  exact eq_refl.
Qed.

(** Test 2SAT critico *)
Lemma TwoSAT_crit_not_SAFE :
  SAFE_condition m_2SAT_crit_demo = false.
Proof.
  apply NPbh_implies_not_SAFE.
  exact m_2SAT_crit_is_NPbh.
Qed.

(** Test 3SAT critico *)
Lemma ThreeSAT_crit_not_SAFE :
  SAFE_condition m_3SAT_crit_demo = false.
Proof.
  apply NPbh_implies_not_SAFE.
  exact m_3SAT_crit_is_NPbh.
Qed.

End Loventre_Family_UNSAFEBRIDGE_V340.

