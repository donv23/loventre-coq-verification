(** ========================================================== *)
(**   Loventre 3-SAT – Easy vs Critical Local Comparison       *)
(**   Versione v121 – nessuna SAFE, nessuna CLASS              *)
(**   Obiettivo: mostrare distinzione di regime                *)
(** ========================================================== *)

From Loventre_Core Require Import Loventre_Core_Prelude.
From Loventre_Core Require Import Loventre_Foundation_Types.
From Loventre_Core Require Import Loventre_Foundation_Params.
From Loventre_Core Require Import Loventre_Foundation_Entropy.

From Loventre_Advanced Require Import Loventre_LMetrics_Core.
From Loventre_Advanced Require Import Loventre_Metrics_Bus.
From Loventre_Advanced.Geometry
     Require Import Loventre_Formal_Core
                    Loventre_LMetrics_Phase_Predicates
                    Loventre_LMetrics_Structure.

From Loventre_Advanced.Geometry
     Require Import Loventre_3SAT_Decode_Compute_v104
                    Loventre_3SAT_LMetrics_From_JSON_v120.

(** ---------------------------------------------------------- *)
(**  Easy / Crit Extracted Instances                           *)
(** ---------------------------------------------------------- *)

Definition m3_easy : LMetrics :=
  decode_and_compute_3SAT metrics_3sat_demo_easy.

Definition m3_crit : LMetrics :=
  decode_and_compute_3SAT metrics_3sat_demo_crit.

(** ---------------------------------------------------------- *)
(**  Lemmi elementari                                          *)
(** ---------------------------------------------------------- *)

Lemma m3_easy_not_critical :
  is_critical m3_easy = false.
Proof. reflexivity. Qed.

Lemma m3_crit_is_critical :
  is_critical m3_crit = true.
Proof. reflexivity. Qed.

(** ---------------------------------------------------------- *)
(**  Separazione locale                                        *)
(** ---------------------------------------------------------- *)

Theorem threeSAT_easy_lt_critical_local :
  is_critical m3_easy = false
  /\ is_critical m3_crit = true.
Proof.
  split.
  - exact m3_easy_not_critical.
  - exact m3_crit_is_critical.
Qed.

(** ========================================================== *)
(**             FINE FILE 3SAT EASY-CRIT v121                  *)
(** ========================================================== *)

