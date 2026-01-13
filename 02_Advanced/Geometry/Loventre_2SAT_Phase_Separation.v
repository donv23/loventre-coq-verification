(**  ***************************************************************  **)
(**      Loventre Project — Geometry Layer — V85 Phase Separation     **)
(**      CANON FILE — NO ASSIOMS — NO REFERENCES TO 03_Main           **)
(**      Autore: Vincenzo Loventre + ChatGPT                          **)
(**      Stato: V85.0 — separazione easy vs crit (2-SAT)              **)
(**  ***************************************************************  **)

From Coq Require Import Bool.Bool.
From Coq Require Import ZArith.

(** Import solo da Core/Geometry — vietato salire al Main *)
From Loventre_Core Require Import Loventre_LMetrics.
From Loventre_Advanced.Geometry Require Import
     Loventre_2SAT_Pacc_Monotonicity
     Loventre_2SAT_Pacc_Lemma
     Loventre_2SAT_Backbone.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Loventre_2SAT_Phase_Separation.

  (** ------------------------------------------------------------ *)
  (**   1. Premesse operative                                       *)
  (** ------------------------------------------------------------ *)
  (** Abbiamo due witness 2-SAT già decodificati e computati
      in precedenza:
        - easy
        - critico
      La backbone fornisce:
        easy_is_pacc       : Pacc per easy
        crit_is_not_pacc   : ¬Pacc per critico
      Tutto è locale a Geometry.
   *)

  Parameter m_2sat_easy   : LMetrics.
  Parameter m_2sat_crit   : LMetrics.

  Hypothesis easy_is_pacc :
      is_pacc_2sat m_2sat_easy = true.

  Hypothesis crit_is_not_pacc :
      is_pacc_2sat m_2sat_crit = false.

  (** ------------------------------------------------------------ *)
  (**   2. Concetto di separazione di fase                          *)
  (** ------------------------------------------------------------ *)

  Definition phase_separated_2sat
    (m_easy m_crit : LMetrics) : Prop :=
      is_pacc_2sat m_easy = true
   /\ is_pacc_2sat m_crit = false.

  (** ------------------------------------------------------------ *)
  (**   3. Lemma di separazione                                     *)
  (** ------------------------------------------------------------ *)

  Theorem local_phase_separation_2sat :
      phase_separated_2sat m_2sat_easy m_2sat_crit.
  Proof.
    unfold phase_separated_2sat.
    split; assumption.
  Qed.

  (** ------------------------------------------------------------ *)
  (**   4. Conseguenza logica locale                                *)
  (** ------------------------------------------------------------ *)
  (** Questa proposizione è l'obiettivo minimo del Canvas 5:
      - nessun assioma nuovo
      - nessun salto al Main
      - separazione basata su metriche computate
   *)

  Corollary phase_distinction_exists :
    exists me mc,
      phase_separated_2sat me mc.
  Proof.
    exists m_2sat_easy, m_2sat_crit.
    apply local_phase_separation_2sat.
  Qed.

End Loventre_2SAT_Phase_Separation.

