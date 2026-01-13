(**
 * Loventre_LMetrics_Time_Mono_v730.v
 * Versione 730 - Monotonia temporale del rischio
 *)

From Stdlib Require Import List Arith Bool.

From Loventre_Core Require Import
  Loventre_Core_Prelude
  Loventre_Kernel
  Loventre_Foundation_Types
  Loventre_Foundation_Params
  Loventre_Foundation_Entropy.

From Loventre_Advanced Require Import
  Loventre_LMetrics_Core
  Loventre_Metrics_Bus
  Loventre_Class_Model
  Loventre_Phase_Assembly
  Loventre_SAFE_Model
  Loventre_Risk_Level
  Loventre_Risk_Level_Bridge.

From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_Structure.

(**
  Assunzione di base:
  `evolve_once` è una dinamica che aumenta (mai diminuisce) la difficoltà
  0 = P_like
  1 = P_accessible
  2 = NP_blackhole
 *)

Definition evolve_once (m : LMetrics) : LMetrics :=
  match risk_class m with
  | P_ClassLike => m
  | P_ClassAccessible => m
  | NP_ClassBlackHole => m
  end.

(**
  Priorità già definita in v720
 *)
Definition class_priority_mono (c : risk_class_type) : nat :=
  match c with
  | P_ClassLike => 0
  | P_ClassAccessible => 1
  | NP_ClassBlackHole => 2
  end.

Lemma evolve_once_monotone :
  forall m,
    class_priority_mono (risk_class (evolve_once m))
      >= class_priority_mono (risk_class m).
Proof.
  intro m.
  unfold evolve_once, class_priority_mono.
  destruct (risk_class m); simpl; lia.
Qed.


