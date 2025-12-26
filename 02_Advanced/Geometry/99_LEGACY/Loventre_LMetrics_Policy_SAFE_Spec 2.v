(* Loventre_LMetrics_Policy_SAFE_Spec

   Specifica ideale aggiuntiva sulla SAFE-ness:

     - Se la decisione globale è [GD_safe], il colore globale
       deve essere [GC_green].

   Questo modulo vive nello stesso "mondo LMetrics" di
   Loventre_LMetrics_Existence_Summary e Loventre_LMetrics_Phase_Predicates,
   basato su Loventre_LMetrics_JSON_Witness.
*)

From Loventre_Geometry Require Import
  Loventre_LMetrics_JSON_Witness
  Loventre_LMetrics_Existence_Summary
  Loventre_LMetrics_Phase_Predicates.

Module JSONW := Loventre_LMetrics_JSON_Witness.
Module Ex    := Loventre_LMetrics_Existence_Summary.
Module Phase := Loventre_LMetrics_Phase_Predicates.

Import JSONW.

(* Spec punto-per-punto: se la decisione è SAFE, il colore è GREEN. *)
Definition policy_SAFE_implies_green_pointwise (m : LMetrics) : Prop :=
  loventre_global_decision m = GD_safe ->
  loventre_global_color m = GC_green.

(* Spec globale: vale per tutti gli stati metrici. *)
Definition policy_SAFE_implies_green_global : Prop :=
  forall m : LMetrics, policy_SAFE_implies_green_pointwise m.

(* Piccolo goal di sanity. *)
Goal True. exact I. Qed.

