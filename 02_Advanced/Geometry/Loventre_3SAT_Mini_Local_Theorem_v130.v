(**************************************************************************)
(* Loventre_3SAT_Mini_Local_Theorem_v130.v                               *)
(* GENNAIO 2026                                                           *)
(* Mini Teorema Locale 3SAT: Pacc ≠ NP_blackhole nel modello locale       *)
(**************************************************************************)

From Loventre_Core Require Import Loventre_Core_Prelude.
From Loventre_Advanced Require Import
     Loventre_LMetrics_Core
     Loventre_Metrics_Bus
     Loventre_Class_Model
     Loventre_SAFE_Model
     Loventre_Class_Properties
     Loventre_Phase_Assembly.

From Loventre_Advanced.Geometry Require Import
     Loventre_3SAT_LMetrics_From_JSON_v120
     Loventre_3SAT_Decode_Compute_v104
     Loventre_3SAT_SAFE_Local_v122
     Loventre_3SAT_Class_Local_v123.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
   MINI-TEOREMA:
   Se l'istanza 3SAT locale ha struttura crit_not_SAFE,
   allora non è Pacc, bensì NP_blackhole.
   Inoltre non può essere simultaneamente Pacc e Blackhole.

   NOTA: nessun Axiom. Prove costruttive elementari.
*)

Lemma crit_not_safe_implies_blackhole
      (m : LMetrics) :
  is_Loventre_3SAT_crit_not_SAFE m ->
  NP_blackhole_Loventre m.
Proof.
  intros Hcrit.
  unfold is_Loventre_3SAT_crit_not_SAFE in Hcrit.
  destruct Hcrit as [Hcrit Hnot].
  unfold NP_blackhole_Loventre.
  unfold phase_crit_NOTSAFE_blackhole.
  exact Hnot.
Qed.

Lemma easy_or_crit_safe_implies_Pacc
      (m : LMetrics) :
  is_Loventre_3SAT_easy m \/ is_Loventre_3SAT_crit_SAFE m ->
  Pacc_Loventre m.
Proof.
  intros H.
  destruct H as [Heasy | Hcs].
  - apply easy_implies_Pacc; exact Heasy.
  - apply crit_SAFE_implies_Pacc; exact Hcs.
Qed.

Lemma no_overlap_Pacc_blackhole
      (m : LMetrics) :
  ~(Pacc_Loventre m /\ NP_blackhole_Loventre m).
Proof.
  intros [HPacc HBH].
  apply (Pacc_never_blackhole m); split; assumption.
Qed.

Theorem loventre_3SAT_local_mini_separation :
  forall m : LMetrics,
    (is_Loventre_3SAT_easy m -> Pacc_Loventre m)
    /\
    (is_Loventre_3SAT_crit_SAFE m -> Pacc_Loventre m)
    /\
    (is_Loventre_3SAT_crit_not_SAFE m -> NP_blackhole_Loventre m)
    /\
    ~(Pacc_Loventre m /\ NP_blackhole_Loventre m).
Proof.
  intro m.
  repeat split.
  - intro Heasy. apply easy_or_crit_safe_implies_Pacc. left; exact Heasy.
  - intro Hcs. apply easy_or_crit_safe_implies_Pacc. right; exact Hcs.
  - intro Hcrit. apply crit_not_safe_implies_blackhole; exact Hcrit.
  - apply no_overlap_Pacc_blackhole.
Qed.

Print loventre_3SAT_local_mini_separation.

(**************************************************************************)
(* FINE FILE                                                              *)
(**************************************************************************)

