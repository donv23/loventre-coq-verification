(**
 * Loventre_LMetrics_Time_Semigroup_v740.v
 * Versione 740 — Struttura semigruppo del tempo
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
  Versione astratta della dinamica temporale:
  evolve_once — passo singolo
 *)

Definition evolve_once (m : LMetrics) : LMetrics :=
  match risk_class m with
  | P_ClassLike => m
  | P_ClassAccessible => m
  | NP_ClassBlackHole => m
  end.

(** Composizione di due passi *)
Definition evolve_twice (m : LMetrics) : LMetrics :=
  evolve_once (evolve_once m).

(** Priorità di rischio definita in V730 *)
Definition class_priority_v740 (c : risk_class_type) : nat :=
  match c with
  | P_ClassLike => 0
  | P_ClassAccessible => 1
  | NP_ClassBlackHole => 2
  end.

(**
  Lemma: un passo non migliora mai.
 *)
Lemma evolve_once_monotone_v740 :
  forall m,
    class_priority_v740 (risk_class (evolve_once m))
      >= class_priority_v740 (risk_class m).
Proof.
  intro m.
  destruct (risk_class m); simpl; lia.
Qed.

(**
  Lemma: la composizione di due passi è monotona.
 *)
Lemma evolve_twice_monotone_v740 :
  forall m,
    class_priority_v740 (risk_class (evolve_twice m))
      >= class_priority_v740 (risk_class m).
Proof.
  intro m.
  unfold evolve_twice.
  destruct (risk_class m); simpl; lia.
Qed.

(**
  Lemma: un passo singolo è idempotente (data la definizione v7xx).
  cioè fare 2 evoluzioni è uguale a una sola:
 *)
Lemma evolve_once_idempotent :
  forall m, evolve_twice m = evolve_once m.
Proof.
  intro m.
  destruct (risk_class m); reflexivity.
Qed.

