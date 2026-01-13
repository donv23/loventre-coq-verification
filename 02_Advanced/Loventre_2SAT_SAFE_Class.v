(**  ***************************************************************  **)
(**        Loventre Project — Class Layer — V89 SAFE Bridge          **)
(**        CANON FILE — NO ASSIOMS — MINIMAL MAIN-READY              **)
(**        Autore: Vincenzo Loventre + ChatGPT                       **)
(**        Stato: V89 — SAFE/Class Model da Geometry                 **) 
(**  ***************************************************************  **)

From Coq Require Import Bool.Bool.

From Loventre_Core Require Import Loventre_LMetrics.

(** Import da Geometry, ma esportiamo concetto in Class Model *)
From Loventre_Advanced.Geometry Require Import
     Loventre_LMetrics_Phase_Predicates
     Loventre_2SAT_Pacc_Class_Bridge
     Loventre_2SAT_SAFE_Bridge
     Loventre_2SAT_Local_Family.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Loventre_2SAT_SAFE_Class.

  (** ------------------------------------------------------------ *)
  (** 1. Definizioni Class Model (estratte dai lemmi Geometry)      *)
  (** ------------------------------------------------------------ *)

  (** Classe Pacc interna globale *)
  Definition In_Pacc_Loventre (m : LMetrics) : Prop :=
    is_pacc_2sat m = true.

  (** Classe NPbh interna globale *)
  Definition In_NPbh_Loventre (m : LMetrics) : Prop :=
    is_pacc_2sat m = false.

  (** SAFE come classe globale *)
  Definition SAFE_Loventre (m : LMetrics) : Prop :=
    In_Pacc_Loventre m.

  (** NON SAFE come classe globale *)
  Definition NotSAFE_Loventre (m : LMetrics) : Prop :=
    In_NPbh_Loventre m.

  (** ------------------------------------------------------------ *)
  (** 2. Lemmi: rispecchiamento diretto da Geometry                 *)
  (** ------------------------------------------------------------ *)

  (** Se un m è SAFE_local in Geometry -> SAFE_Loventre nel Model *)
  Lemma SAFE_local_to_class :
      forall m, SAFE_local m -> SAFE_Loventre m.
  Proof.
    intros m H.
    unfold SAFE_local, SAFE_Loventre, In_Pacc_Loventre in *.
    exact H.
  Qed.

  Lemma nonSAFE_local_to_class :
      forall m, nonSAFE_local m -> NotSAFE_Loventre m.
  Proof.
    intros m H.
    unfold nonSAFE_local, NotSAFE_Loventre, In_NPbh_Loventre in *.
    exact H.
  Qed.

  (** ------------------------------------------------------------ *)
  (** 3. Famiglie: ereditarietà del risultato                       *)
  (** ------------------------------------------------------------ *)

  Parameter easy_family : list LMetrics.
  Parameter crit_family : list LMetrics.

  Hypothesis all_easy_SAFE_local :
      forall m, In m easy_family -> SAFE_local m.

  Hypothesis all_crit_NONSAFE_local :
      forall m, In m crit_family -> nonSAFE_local m.

  Lemma all_easy_SAFE_class :
      forall m, In m easy_family -> SAFE_Loventre m.
  Proof.
    intros m Hin.
    apply SAFE_local_to_class.
    apply all_easy_SAFE_local.
    exact Hin.
  Qed.

  Lemma all_crit_NONSAFE_class :
      forall m, In m crit_family -> NotSAFE_Loventre m.
  Proof.
    intros m Hin.
    apply nonSAFE_local_to_class.
    apply all_crit_NONSAFE_local.
    exact Hin.
  Qed.

  (** ------------------------------------------------------------ *)
  (** 4. Primo risultato di classe                                 *)
  (** ------------------------------------------------------------ *)

  Theorem class_split_2sat :
      (forall m, In m easy_family -> SAFE_Loventre m)
   /\ (forall m, In m crit_family -> NotSAFE_Loventre m).
  Proof.
    split.
    - apply all_easy_SAFE_class.
    - apply all_crit_NONSAFE_class.
  Qed.

End Loventre_2SAT_SAFE_Class.

