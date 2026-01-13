(** Loventre_LMetrics_Import_2SAT.v
    Importazione minima dei due dataset 2SAT easy/crit.
    Canonico, senza side effects.
*)

From Loventre_Core Require Import
  Loventre_Kernel
  Loventre_Foundation_Types.

From Loventre_Advanced Require Import
  Loventre_Class_Model
  Loventre_SAFE_Model
  Loventre_Phase_Assembly.

From Loventre_Advanced.Geometry Require Import
  Loventre_Formal_Core
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_Structure.

From Loventre_Advanced Require Import
  Loventre_LMetrics_JSON_Witness.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Easy 2SAT metrics *)
Definition m_easy : M :=
  load_json_lmetrics "data/lmetrics/m_2SAT_easy.json".

(** Critical 2SAT metrics *)
Definition m_crit : M :=
  load_json_lmetrics "data/lmetrics/m_2SAT_crit.json".

(** Predicati di fase estratti dalla metrica *)

Definition easy_is_P : Prop := Phase_P_like m_easy.
Definition easy_is_Pacc : Prop := Phase_P_accessible m_easy.
Definition easy_is_BH : Prop := Phase_NP_blackhole m_easy.

Definition crit_is_P : Prop := Phase_P_like m_crit.
Definition crit_is_Pacc : Prop := Phase_P_accessible m_crit.
Definition crit_is_BH : Prop := Phase_NP_blackhole m_crit.

(** Teoremi fumati semplici (scatta errore se incoerenti) *)

Theorem easy_not_bh_and_p :
  easy_is_BH -> easy_is_P -> False.
Proof.
  unfold easy_is_BH, easy_is_P, Phase_NP_blackhole, Phase_P_like.
  apply In_NPbh_Lov_not_P.
Qed.

Theorem crit_not_p_and_bh :
  crit_is_P -> crit_is_BH -> False.
Proof.
  unfold crit_is_BH, crit_is_P, Phase_NP_blackhole, Phase_P_like.
  apply In_NPbh_Lov_not_P.
Qed.

