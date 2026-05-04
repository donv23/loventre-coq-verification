(* Loventre_LMetrics_Separation_Program

   Programma di separazione globale per l'asse LMetrics + Policy.

   Obiettivo di questo file:

   - mettere insieme la "tripla esistenza"
       P_like, P_like_accessible, NP_like-black-hole
     formalizzata in Geometry;

   - il Core Program di Policy
       (esistenza P/NP_like-black-hole + policy_ideal_spec);

   - e il teorema decisionale
       NP_like-black-hole ⇒ NON SAFE

     in una singola proposizione "di programma" che funge da
     mini-Teorema di Loventre sul livello LMetrics + Policy.
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
  Loventre_LMetrics_Policy_Theorem.

Module JSONW    := Loventre_LMetrics_JSON_Witness.
Module Ex       := Loventre_LMetrics_Existence_Summary.
Module Phase    := Loventre_LMetrics_Phase_Predicates.
Module PolSpec  := Loventre_LMetrics_Policy_Spec.
Module SafeSpec := Loventre_LMetrics_Policy_SAFE_Spec.
Module AccEx    := Loventre_LMetrics_Accessible_Existence.
Module Core     := Loventre_LMetrics_Policy_Specs.
Module Thm      := Loventre_LMetrics_Policy_Theorem.

Import JSONW.
Import Ex Phase.

(* ------------------------------------------------------------------ *)
(* 1. Proposizione "tripla esistenziale" P / P_accessible / NP_like.  *)
(* ------------------------------------------------------------------ *)

(* Questa proposizione è la controparte logica della tripla esistenziale
   formalizzata in Geometry (Loventre_LMetrics_Accessible_Existence.v).

   Essa dice:

     - esiste almeno una configurazione is_P_like;
     - esiste almeno una configurazione is_P_like_accessible;
     - esiste almeno una configurazione is_NP_like_black_hole.
*)

Definition Loventre_P_Paccessible_NP_like_triple_prop : Prop :=
  (exists m : LMetrics, is_P_like m)
  /\
  (exists m : LMetrics, is_P_like_accessible m)
  /\
  (exists m : LMetrics, is_NP_like_black_hole m).

(* In Geometry abbiamo già un teorema che realizza questa proposizione:

     Theorem Loventre_P_Paccessible_NP_like_triple_exist :
       Loventre_P_Paccessible_NP_like_triple_prop.

   Qui lo importiamo "così com'è", come prova della proposizione sopra.
*)

Lemma Loventre_P_Paccessible_NP_like_triple_from_Geometry :
  Loventre_P_Paccessible_NP_like_triple_prop.
Proof.
  exact AccEx.Loventre_P_Paccessible_NP_like_triple_exist.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. Proposizione di separazione decisionale NP_like-black-hole.     *)
(* ------------------------------------------------------------------ *)

(* Dal file Loventre_LMetrics_Policy_Theorem abbiamo già:

     Definition Loventre_SAFE_separation_prop : Prop :=
       forall m : LMetrics,
         Ex.is_NP_like_black_hole m ->
         loventre_global_decision m <> GD_safe.

   che esprime esattamente:

     "Nessuna configurazione NP_like-black-hole può essere SAFE".
*)

(* La ripeschiamo con un alias più breve. *)
Definition Loventre_SAFE_separation_prop_alias : Prop :=
  Thm.Loventre_SAFE_separation_prop.

(* E ridichiariamo anche il teorema che la dimostra a partire dal
   Core Program di Policy e dalla spec SAFE. *)
Lemma Loventre_SAFE_separation_from_core_and_SAFE_spec_alias :
  Core.Loventre_Policy_Core_Program ->
  SafeSpec.policy_SAFE_implies_green_global ->
  Loventre_SAFE_separation_prop_alias.
Proof.
  intros Hcore Hsafe.
  apply Thm.Loventre_SAFE_separation_from_core_and_SAFE_spec; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. Programma di separazione globale Loventre LMetrics + Policy.    *)
(* ------------------------------------------------------------------ *)

(* Questa è la proposizione che sintetizza il "mini-Teorema di Loventre"
   al livello LMetrics + Policy:

   - tripla esistenza di fasi:
       P_like, P_like_accessible, NP_like-black-hole;

   - separazione decisionale:
       NP_like-black-hole ⇒ NON SAFE.
*)

Definition Loventre_LMetrics_Separation_Statement : Prop :=
  Loventre_P_Paccessible_NP_like_triple_prop
  /\
  Loventre_SAFE_separation_prop_alias.

(* Teorema principale di questo file:

   Se assumiamo:
     - il Core Program di Policy (esistenza P / NP_like-black-hole
       + policy_ideal_spec);
     - la spec SAFE (GD_safe ⇒ GC_green);

   allora vale la proposizione di separazione globale
   [Loventre_LMetrics_Separation_Statement].
*)

Theorem Loventre_LMetrics_Separation_Theorem_from_core_and_SAFE :
  Core.Loventre_Policy_Core_Program ->
  SafeSpec.policy_SAFE_implies_green_global ->
  Loventre_LMetrics_Separation_Statement.
Proof.
  intros Hcore Hsafe.
  unfold Loventre_LMetrics_Separation_Statement.
  split.
  - (* Tripla esistenza P / P_accessible / NP_like-black-hole. *)
    apply Loventre_P_Paccessible_NP_like_triple_from_Geometry.
  - (* Separazione decisionale NP_like-black-hole ⇒ NON SAFE. *)
    apply Loventre_SAFE_separation_from_core_and_SAFE_spec_alias; assumption.
Qed.

(* Piccolo goal di sanity. *)
Goal True. exact I. Qed.

