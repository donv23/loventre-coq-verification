(*
  Loventre_3SAT_Test_All_v124.v
  Test locale di coerenza per 3-SAT: easy vs critico vs BH
  Nessuna prova complessa: solo pattern sanity
  Nessun Admitted, nessun assioma
*)

From Loventre_Core Require Import Loventre_Core_Prelude.
From Loventre_Advanced Require Import
     Loventre_LMetrics_Core
     Loventre_Metrics_Bus
     Loventre_SAFE_Model
     Loventre_Class_Model
     Loventre_Class_Properties
     Loventre_Phase_Assembly.
From Loventre_Advanced.Geometry Require Import
     Loventre_Formal_Core
     Loventre_LMetrics_Phase_Predicates
     Loventre_LMetrics_Structure
     Loventre_3SAT_LMetrics_From_JSON_v120
     Loventre_3SAT_EasyCrit_Compare_v121
     Loventre_3SAT_SAFE_Local_v122
     Loventre_3SAT_Class_Local_v123.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Loventre3SATTestAll_v124.

  (*** Test Easy instance ***)

  Lemma easy_is_SAFE_and_Pacc :
    forall m, is_easy_3SAT m = true ->
      SAFE_3SAT_local m /\ In_Pacc_Lov 3SAT_local_class m.
  Proof.
    intros m H.
    pose proof SAFE_easy_3SAT m H as HS.
    pose proof easy_in_Pacc_3SAT m H as HP.
    split; assumption.
  Qed.

  (*** Test Critical SAFE instance ***)

  Lemma crit_SAFE_is_Pacc :
    forall m, is_crit_SAFE_3SAT m = true ->
      SAFE_3SAT_local m /\ In_Pacc_Lov 3SAT_local_class m.
  Proof.
    intros m H.
    pose proof SAFE_crit_3SAT m H as HS.
    pose proof crit_SAFE_in_Pacc_3SAT m H as HP.
    split; assumption.
  Qed.

  (*** Test Critical non SAFE instance → BH ***)

  Lemma crit_not_SAFE_is_BH :
    forall m, is_crit_not_SAFE_3SAT m = true ->
      (~ SAFE_3SAT_local m) /\ In_NP_blackhole_Lov 3SAT_local_class m.
  Proof.
    intros m H.
    pose proof crit_not_SAFE_not_SAFE_3SAT m H as Hn.
    pose proof crit_not_SAFE_in_BH_3SAT m H as HB.
    split; assumption.
  Qed.

  (*** Mini sanity: esclusione Pacc/BH ***)

  Lemma no_overlap_Pacc_BH :
    forall m,
      In_Pacc_Lov 3SAT_local_class m ->
      In_NP_blackhole_Lov 3SAT_local_class m ->
      False.
  Proof.
    intros m HP HB.
    eapply class_Pacc_not_BH; eauto.
  Qed.

  (*** Mini sanity: se crit non SAFE, non può essere Pacc ***)

  Lemma crit_non_SAFE_not_Pacc :
    forall m, is_crit_not_SAFE_3SAT m = true ->
      ~ In_Pacc_Lov 3SAT_local_class m.
  Proof.
    intros m Hcrit HP.
    pose proof crit_not_SAFE_in_BH_3SAT m Hcrit as HB.
    eapply no_overlap_Pacc_BH; eauto.
  Qed.

End Loventre3SATTestAll_v124.


