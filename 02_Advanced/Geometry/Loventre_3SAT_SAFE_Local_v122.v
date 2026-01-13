(** ============================================================= *)
(** Loventre_3SAT_SAFE_Local_v122.v                               *)
(** Prima dimostrazione SAFE/easy e NON SAFE/crit per 3SAT        *)
(** Locale — senza coinvolgere Class, Bridge, né NP-bh            *)
(** ============================================================= *)

From Loventre_Core Require Import Loventre_Core_Prelude.
From Loventre_Advanced Require Import
  Loventre_LMetrics_Core
  Loventre_Metrics_Bus
  Loventre_SAFE_Model
  Loventre_Phase_Assembly.
From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Structure
  Loventre_3SAT_LMetrics_From_JSON_v120
  Loventre_3SAT_Decode_Compute_v104
  Loventre_3SAT_EasyCrit_Compare_v121.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ------------------------------------------------------------- *)
(**  Obiettivo locale                                             *)
(**  m3_easy  = profilo 3SAT facile  → SAFE                       *)
(**  m3_crit  = profilo 3SAT critico → NON SAFE                   *)
(** ------------------------------------------------------------- *)

Lemma m3_easy_is_SAFE_local :
  is_safe (compute_safe_flag m3_easy_core).
Proof.
  unfold compute_safe_flag.
  unfold m3_easy_core.
  simpl.
  (** m3_easy_core ha V0 < barrier, rischio basso *)
  exact I.
Qed.

Lemma m3_crit_is_NOT_SAFE_local :
  is_not_safe (compute_safe_flag m3_crit_core).
Proof.
  unfold compute_safe_flag.
  unfold m3_crit_core.
  simpl.
  (** m3_crit_core ha V0 alto + tunneling quasi nullo *)
  exact I.
Qed.

(** ------------------------------------------------------------- *)
(**  Versione riassuntiva                                         *)
(** ------------------------------------------------------------- *)

Theorem Loventre_3SAT_Local_SAFE_Profile_v122 :
  is_safe (compute_safe_flag m3_easy_core)
  /\ is_not_safe (compute_safe_flag m3_crit_core).
Proof.
  split.
  - apply m3_easy_is_SAFE_local.
  - apply m3_crit_is_NOT_SAFE_local.
Qed.

(** ============================================================= *)
(** Fine file                                                     *)
(** ============================================================= *)

