(**
  Loventre_3SAT_Class_Local_v123.v
  --------------------------------
  Primo bridging locale tra SAFE / NOT SAFE e classi Pacc / BH
  per il dominio 3-SAT, senza dipendenze da 03_Main.

  Obiettivi locali V123:
    • SAFE_easy   → In_Pacc_Lov (locale)
    • SAFE_crit   → In_Pacc_Lov (locale)
    • NOT SAFE    → In_NP_blackhole_Lov (locale)

  Questa è una traduzione diretta e minimale dei predicati
  definiti in:
     - Loventre_LMetrics_Phase_Predicates
     - Loventre_SAFE_Model
     - Loventre_Class_Model
*)

From Loventre_Core Require Import Loventre_Core_Prelude.
From Loventre_Advanced Require Import
     Loventre_LMetrics_Core
     Loventre_LMetrics_Structure
     Loventre_LMetrics_Phase_Predicates
     Loventre_SAFE_Model
     Loventre_Class_Model.

(********************************************************************)
(** Locale 3SAT SAFE -> Pacc                                        *)
(********************************************************************)

(** Easy-SAFE produce Pacc a livello locale *)
Lemma loventre_3sat_easy_safe_implies_pacc_local :
  forall (m : LMetrics),
    loventre_SAFE_easy m ->
    loventre_In_Pacc_Lov m.
Proof.
  intros m Hsafe.
  (** La definizione di In_Pacc_Lov è coerente con SAFE_easy *)
  exact (loventre_SAFE_easy_refines_Pacc m Hsafe).
Qed.

(** Crit-SAFE produce Pacc a livello locale *)
Lemma loventre_3sat_crit_safe_implies_pacc_local :
  forall (m : LMetrics),
    loventre_SAFE_crit m ->
    loventre_In_Pacc_Lov m.
Proof.
  intros m Hsafe.
  exact (loventre_SAFE_crit_refines_Pacc m Hsafe).
Qed.

(********************************************************************)
(** Locale 3SAT NOT SAFE -> BH                                      *)
(********************************************************************)

(** Un m 3SAT non SAFE appartiene alla classe NP-blackhole *)
Lemma loventre_3sat_not_safe_implies_npbh_local :
  forall (m : LMetrics),
    loventre_not_SAFE m ->
    loventre_In_NP_blackhole_Lov m.
Proof.
  intros m Hns.
  exact (loventre_not_SAFE_refines_NPbh m Hns).
Qed.

(********************************************************************)
(** Sanity lemma: nessun caso “orfano”                              *)
(********************************************************************)

Lemma loventre_3sat_safe_or_bh_local :
  forall (m : LMetrics),
    loventre_SAFE_easy m \/
    loventre_SAFE_crit m \/
    loventre_not_SAFE m ->
    loventre_In_Pacc_Lov m \/
    loventre_In_NP_blackhole_Lov m.
Proof.
  intros m H.
  destruct H as [Heasy | [Hcrit | Hns]].
  - left.  exact (loventre_SAFE_easy_refines_Pacc m Heasy).
  - left.  exact (loventre_SAFE_crit_refines_Pacc m Hcrit).
  - right. exact (loventre_not_SAFE_refines_NPbh m Hns).
Qed.

(********************************************************************)
(** Fine                                                            *)
(********************************************************************)


