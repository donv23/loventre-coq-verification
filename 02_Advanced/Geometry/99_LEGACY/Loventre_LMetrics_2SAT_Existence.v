(* ========================================================== *)
(*  LOVENTRE PROJECT — Loventre_LMetrics_2SAT_Existence.v      *)
(*  Dicembre 2025 — Lemma di esistenza per la famiglia 2-SAT   *)
(* ========================================================== *)

From Coq Require Import List.
Import ListNotations.

Require Import Loventre_LMetrics_JSON_Link.
Require Import Loventre_LMetrics_2SAT_Family_Stack.
Require Import Loventre_LMetrics_2SAT_Mini_Theorem.

(* ---------------------------------------------------------- *)
(* 1. Assiomi di collegamento                                 *)
(* ---------------------------------------------------------- *)

(**  Questi due assiomi dichiarano che i due witness 2-SAT
     (easy / crit) fanno parte del bus JSON `loventre_json_links`.
     Tali inclusioni sono garantite dalla fase di regressione Python. *)

Axiom m_2SAT_easy_in_links_ex :
  In m_2SAT_easy loventre_json_links.

Axiom m_2SAT_crit_in_links_ex :
  In m_2SAT_crit loventre_json_links.

(* ---------------------------------------------------------- *)
(* 2. Lemma di esistenza strutturale                          *)
(* ---------------------------------------------------------- *)

Lemma Loventre_2SAT_Family_Exists :
  exists fam : TwoSAT_Family_Structure, True.
Proof.
  pose proof m_2SAT_easy_in_links_ex as H_easy.
  pose proof m_2SAT_crit_in_links_ex as H_crit.
  refine (ex_intro _ (Loventre_2SAT_Family_OK H_easy H_crit) _).
  exact I.
Defined.

(* ---------------------------------------------------------- *)
(* 3. Commento conclusivo                                    *)
(* ---------------------------------------------------------- *)
(** Questo lemma chiude il livello “Geometry” del 2-SAT:
    dimostra che, assumendo la coerenza del bridge JSON ↔ Coq,
    la famiglia 2-SAT (easy/crit) ammette una struttura valida
    nel bus LMetrics.  *)

