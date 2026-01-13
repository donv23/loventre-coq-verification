(* =============================================================== *)
(* Loventre_Main_2SAT_Validation_Chain.v                           *)
(* Consolidamento V93 – Catena completa 2SAT verificata            *)
(* GENNAIO 2026                                                    *)
(* =============================================================== *)

From Loventre_Core        Require Import Loventre_Core_Prelude.
From Loventre_Advanced    Require Import
     Loventre_Metrics_Bus
     Loventre_Class_Model
     Loventre_Class_Properties
     Loventre_Phase_Assembly.
From Loventre_Advanced.Geometry Require Import
     Loventre_2SAT_LMetrics_From_JSON
     Loventre_2SAT_Decode_Compute
     Loventre_2SAT_EasyCrit_Compare
     Loventre_2SAT_Local_Family
     Loventre_2SAT_Pacc_Class_Bridge
     Loventre_2SAT_SAFE_Bridge
     Loventre_2SAT_Mini_Theorem_Extended.

(* --------------------------------------------------------------- *)
(* Step 1: JSON decode/compute produce metriche valide              *)
(* --------------------------------------------------------------- *)

Theorem decode_compute_chain_easy_ok :
  forall m, In m easy_lovelocal_family ->
    pacc_flag m = true
    /\ safe_flag m = true.
Proof.
  intros m Hm.
  split.
  - apply pacc_easy_family_flag_true. exact Hm.
  - apply safe_easy_family_flag_true. exact Hm.
Qed.

Theorem decode_compute_chain_crit_ok :
  forall m, In m crit_lovelocal_family ->
    pacc_flag m = false.
Proof.
  intros m Hm.
  apply pacc_crit_family_flag_false. exact Hm.
Qed.

(* --------------------------------------------------------------- *)
(* Step 2: Bridge classi e semantica SAFE                           *)
(* --------------------------------------------------------------- *)

Theorem easy_implies_Pacc_and_SAFE :
  forall m, In m easy_lovelocal_family ->
    In_Pacc_Lov m /\ is_safe m.
Proof.
  intros m Hm. split.
  - apply easy_family_all_in_Pacc. exact Hm.
  - apply safe_easy_family_is_safe. exact Hm.
Qed.

Theorem crit_implies_NPbh_and_NotSAFE :
  forall m, In m crit_lovelocal_family ->
    In_NP_BlackHole_Lov m /\ ~ is_safe m.
Proof.
  intros m Hm. split.
  - apply crit_family_all_in_NPbh. exact Hm.
  - apply crit_family_not_safe. exact Hm.
Qed.

(* --------------------------------------------------------------- *)
(* Step 3: Mini separazione + nessuna collisione                    *)
(* --------------------------------------------------------------- *)

Theorem easy_and_crit_separate_on_flags :
  forall m, In m easy_lovelocal_family -> ~ In m crit_lovelocal_family.
Proof.
  intros m He Hc.
  apply easy_crit_family_disjoint with (m := m); assumption.
Qed.

(* --------------------------------------------------------------- *)
(* Step 4: Conclusione catena completa                              *)
(* --------------------------------------------------------------- *)

Theorem Loventre_2SAT_Validation_Chain_OK :
  (forall m, In m easy_lovelocal_family ->
            In_Pacc_Lov m /\ is_safe m)
  /\
  (forall m, In m crit_lovelocal_family ->
            In_NP_BlackHole_Lov m /\ ~ is_safe m)
  /\
  (forall m, In m easy_lovelocal_family -> ~ In m crit_lovelocal_family).
Proof.
  repeat split.
  - apply easy_implies_Pacc_and_SAFE.
  - apply crit_implies_NPbh_and_NotSAFE.
  - apply easy_and_crit_separate_on_flags.
Qed.

(* =============================================================== *)
(* FINE V93 – Tutta la pipeline dimostrata senza nuovi Axiom       *)
(* =============================================================== *)

