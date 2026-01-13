(* Loventre_Theorem_v1.v

   Versione 1 del "Teorema di Loventre" a livello LMetrics + Policy.

   Obiettivo di questo file:

   - prendere come ingredienti:
       * la tripla esistenza P / P_accessible / NP_like-black-hole;
       * il programma di separazione LMetrics + Policy;
       * il lemma esistenziale su un witness NP_like-black-hole NON SAFE;

   - e incapsulare tutto in una proposizione globale:

       Loventre_Theorem_v1_Statement : Prop

     dimostrata a partire dal contratto di Policy:

       - Core.Loventre_Policy_Core_Program
       - SafeSpec.policy_SAFE_implies_green_global.
*)

From Loventre_Geometry Require Import
  Loventre_LMetrics_JSON_Witness
  Loventre_LMetrics_Existence_Summary
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_Policy_Spec
  Loventre_LMetrics_Policy_SAFE_Spec
  Loventre_LMetrics_Accessible_Existence.

From Loventre_Main Require Import
  Loventre_LMetrics_Policy_Specs
  Loventre_LMetrics_Policy_Theorem
  Loventre_LMetrics_Separation_Program
  Loventre_LMetrics_Witness_Separation.

Module JSONW    := Loventre_LMetrics_JSON_Witness.
Module Ex       := Loventre_LMetrics_Existence_Summary.
Module Phase    := Loventre_LMetrics_Phase_Predicates.
Module PolSpec  := Loventre_LMetrics_Policy_Spec.
Module SafeSpec := Loventre_LMetrics_Policy_SAFE_Spec.
Module AccEx    := Loventre_LMetrics_Accessible_Existence.
Module Core     := Loventre_LMetrics_Policy_Specs.
Module Thm      := Loventre_LMetrics_Policy_Theorem.
Module SepProg  := Loventre_LMetrics_Separation_Program.
Module WitSep   := Loventre_LMetrics_Witness_Separation.

Import JSONW Ex Phase.

(* ------------------------------------------------------------------ *)
(* 1. Statement globale di "Teorema di Loventre v1".                  *)
(* ------------------------------------------------------------------ *)

(* Richiamiamo:

   - SepProg.Loventre_LMetrics_Separation_Statement : Prop :=
       Loventre_P_Paccessible_NP_like_triple_prop
       /\
       Loventre_SAFE_separation_prop_alias.

     cioè:

       (exists P_like) /\ (exists P_like_accessible)
       /\ (exists NP_like-black-hole)
       /\ (forall NP_like-black-hole, decisione <> SAFE).

   - WitSep.Loventre_SAFE_separation_exists_NP_like_witness_json :
       Core.Loventre_Policy_Core_Program ->
       SafeSpec.policy_SAFE_implies_green_global ->
       exists m : LMetrics,
         Ex.is_NP_like_black_hole m /\
         loventre_global_decision m <> GD_safe.

     cioè: esiste almeno un witness NP_like-black-hole NON SAFE.
*)

Definition Loventre_Theorem_v1_Statement : Prop :=
  SepProg.Loventre_LMetrics_Separation_Statement
  /\
  (exists m : LMetrics,
      Ex.is_NP_like_black_hole m /\
      loventre_global_decision m <> GD_safe).

(* Lettura informale:

   Sotto le ipotesi "di contratto" su LMetrics + Policy:

     - il paesaggio LMetrics contiene:
         * almeno una configurazione P_like;
         * almeno una configurazione P_like_accessible
           (P-like low risk, non-black-hole, borderline + green);
         * almeno una configurazione NP_like-black-hole;

     - ogni configurazione NP_like-black-hole è NON SAFE;

     - esiste almeno un witness NP_like-black-hole concreto (dal mondo
       JSON/metrics) che è effettivamente NON SAFE.

   Questa è la forma v1 del "Teorema di Loventre" lato LMetrics + Policy.
*)

(* ------------------------------------------------------------------ *)
(* 2. Teorema principale: dedurre la Statement dal contratto Policy.  *)
(* ------------------------------------------------------------------ *)

Theorem Loventre_Theorem_v1_from_contract :
  Core.Loventre_Policy_Core_Program ->
  SafeSpec.policy_SAFE_implies_green_global ->
  Loventre_Theorem_v1_Statement.
Proof.
  intros Hcore Hsafe.
  unfold Loventre_Theorem_v1_Statement.
  split.
  - (* Parte 1: programma di separazione globale LMetrics + Policy. *)
    apply SepProg.Loventre_LMetrics_Separation_Theorem_from_core_and_SAFE; assumption.
  - (* Parte 2: esistenza di un witness NP_like-black-hole NON SAFE. *)
    apply WitSep.Loventre_SAFE_separation_exists_NP_like_witness_json; assumption.
Qed.

(* Piccolo goal di sanity. *)
Goal True. exact I. Qed.

