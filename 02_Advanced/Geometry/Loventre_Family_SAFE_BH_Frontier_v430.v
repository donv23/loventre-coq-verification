(***************************************************************************)
(* Loventre Family SAFE vs BlackHole Frontier — V430                       *)
(* Autore: Vincenzo Loventre                                               *)
(* Stato: CANON                                                            *)
(***************************************************************************)

From Loventre_Core Require Import Loventre_Core_Prelude.
From Loventre_Advanced Require Import
  Loventre_LMetrics_Core
  Loventre_Metrics_Bus
  Loventre_SAFE_Model
  Loventre_Class_Model
  Loventre_Phase_Assembly
.
From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_Structure
.

(***************************************************************************)
(** SAFE implies NOT in BlackHole *)
(***************************************************************************)

Lemma SAFE_implies_not_blackhole :
  forall M : LMetrics,
    In_Safe_Loventre M ->
    ~ In_NP_blackhole_Loventre M.
Proof.
  intros M Hsafe Hcontra.
  unfold In_Safe_Loventre in Hsafe.
  unfold In_NP_blackhole_Loventre in Hcontra.
  destruct Hcontra as [HK HB].
  (* Nel modello Loventre, SAFE vuol dire rischio controllato <= barriera *)
  (* mentre NP_blackhole implica barriera insufficiente / collasso *)
  (* Contraddizione strutturale *)
  inversion HK.
Qed.

(***************************************************************************)
(** BlackHole implies NOT SAFE *)
(***************************************************************************)

Lemma blackhole_implies_not_safe :
  forall M : LMetrics,
    In_NP_blackhole_Loventre M ->
    ~ In_Safe_Loventre M.
Proof.
  intros M Hbh Hcontra.
  unfold In_Safe_Loventre in Hcontra.
  unfold In_NP_blackhole_Loventre in Hbh.
  destruct Hbh as [HK HB].
  (* SAFE richiede robustezza > soglia *)
  (* BlackHole fornisce violazione di soglia → contraddizione *)
  inversion HB.
Qed.

(***************************************************************************)
(* Combined statement: SAFE and BlackHole are disjoint                     *)
(***************************************************************************)

Theorem safe_blackhole_disjoint :
  forall M : LMetrics,
    ~ (In_Safe_Loventre M /\ In_NP_blackhole_Loventre M).
Proof.
  intros M [HS Hbh].
  apply (SAFE_implies_not_blackhole M HS Hbh).
Qed.

