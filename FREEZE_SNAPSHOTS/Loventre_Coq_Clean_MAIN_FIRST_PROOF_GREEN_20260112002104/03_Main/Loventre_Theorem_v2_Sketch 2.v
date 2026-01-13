(* Loventre_Theorem_v2_Sketch.v
   Dicembre 2025 – LOVENTRE_THEOREM_V2 (sketch)

   Asse: LMetrics + Policy + SAFE + Profili di complessità

   Scopo:
   - Prendere LOVENTRE_THEOREM_V1 (LMetrics + Policy + SAFE + witness JSON),
   - aggiungere la separazione di complessità su LMetrics
     (Loventre_Complexity_Separation_Statement),
   - formare un unico enunciato "v2" che combina entrambi i livelli.
*)

From Stdlib Require Import Reals.

From Loventre_Geometry Require Import
  Loventre_LMetrics_JSON_Witness
  Loventre_LMetrics_Existence_Summary
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_Policy_Spec
  Loventre_LMetrics_Policy_SAFE_Spec
  Loventre_LMetrics_Accessible_Existence
  Loventre_LMetrics_Complexity_Profiles.

From Loventre_Main Require Import
  Loventre_LMetrics_Policy_Specs
  Loventre_LMetrics_Policy_Theorem
  Loventre_LMetrics_Separation_Program
  Loventre_LMetrics_Witness_Separation
  Loventre_Theorem_v1
  Loventre_Theorem_v1_Corollaries.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

Module JSONW    := Loventre_LMetrics_JSON_Witness.
Module Ex       := Loventre_LMetrics_Existence_Summary.
Module Phase    := Loventre_LMetrics_Phase_Predicates.
Module PolSpec  := Loventre_LMetrics_Policy_Spec.
Module SafeSpec := Loventre_LMetrics_Policy_SAFE_Spec.
Module Core     := Loventre_LMetrics_Policy_Specs.
Module SepProg  := Loventre_LMetrics_Separation_Program.
Module Compl    := Loventre_LMetrics_Complexity_Profiles.

Import JSONW Phase.

(** ------------------------------------------------------------------------ *)
(** 1. Statement di LOVENTRE_THEOREM_V2_SKETCH                               *)
(** ------------------------------------------------------------------------ *)

(**
   Richiamo:

   - Loventre_Theorem_v1_Statement : Prop
       (dal file Loventre_Theorem_v1.v)
     combina:
       * tripla esistenza P_like / P_like_accessible / NP_like-black-hole,
       * separazione decisionale NP_like-black-hole ⇒ NON SAFE,
       * esistenza di almeno un witness NP_like-black-hole NON SAFE (JSON-side).

   - Compl.Loventre_Complexity_Separation_Statement : Prop
       (da Loventre_LMetrics_Complexity_Profiles.v)
     dice:
       forall m,
         NP_like_crit_complexity_profile m ->
         ~ P_like_complexity_profile m.

   In v2 li incolliamo in un unico enunciato.
 *)

Definition Loventre_Theorem_v2_Statement : Prop :=
  Loventre_Theorem_v1_Statement
  /\
  Compl.Loventre_Complexity_Separation_Statement.

(**
   Lettura informale di Loventre_Theorem_v2_Statement:

   Sotto il contratto ideale di Policy (Core Program + SAFE ⇒ GREEN),
   vale contemporaneamente che:

   - esistono fasi P_like, P_like_accessible e NP_like-black-hole,
   - nessuna configurazione NP_like-black-hole è SAFE
     e almeno un witness JSON NP_like-black-hole è NON SAFE,
   - i profili di complessità NP_like_crit e P_like_complexity
     sono separati: nessun m può essere NP_like_crit_complexity_profile
     e P_like_complexity_profile allo stesso tempo.
 *)

(** ------------------------------------------------------------------------ *)
(** 2. Teorema: LOVENTRE_THEOREM_V2 dallo stesso contratto di Policy         *)
(** ------------------------------------------------------------------------ *)

Theorem Loventre_Theorem_v2_from_contract :
  Core.Loventre_Policy_Core_Program ->
  SafeSpec.policy_SAFE_implies_green_global ->
  Loventre_Theorem_v2_Statement.
Proof.
  intros Hcore Hsafe.
  unfold Loventre_Theorem_v2_Statement.
  split.
  - (* Parte v1: LMetrics + Policy + SAFE + witness JSON *)
    apply Loventre_Theorem_v1_from_contract; assumption.
  - (* Parte complessità: separazione NP_like_crit vs P_like_complexity *)
    apply Compl.Loventre_Complexity_Separation.
Qed.

