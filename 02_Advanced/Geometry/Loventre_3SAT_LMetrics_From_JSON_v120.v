(**
  Loventre_3SAT_LMetrics_From_JSON_v120.v
  V120 – 3-SAT canonical JSON → LMetrics bridge
  Nessun assioma. Importa 3SAT easy/crit e li decodifica come LMetrics.
*)

From Loventre_Core      Require Import Loventre_Core_Prelude.
From Loventre_Advanced  Require Import
   Loventre_LMetrics_Core
   Loventre_Metrics_Bus.
From Loventre_Advanced.Geometry Require Import
   Loventre_LMetrics_Phase_Predicates
   Loventre_LMetrics_Structure.
From Loventre_Advanced Require Import
   Loventre_LMetrics_JSON_Witness.

(** Nome radice per 3-SAT *)
Definition p3sat := "3SAT"%string.

(** JSON canonici *)
Definition m_3sat_easy_json  := "JSON_IO/3SAT/m_3SAT_easy_demo.json".
Definition m_3sat_crit_json  := "JSON_IO/3SAT/m_3SAT_crit_demo.json".

(** Decodifica → opzioni di LMetrics *)
Definition m_3sat_easy_opt  : option LMetrics :=
  decode_lmetrics_from_json_file m_3sat_easy_json.

Definition m_3sat_crit_opt  : option LMetrics :=
  decode_lmetrics_from_json_file m_3sat_crit_json.

(** Estrarre testualmente gli LMetrics (solo se Some) *)
Definition m_3sat_easy_lm : Prop :=
  exists lm, m_3sat_easy_opt = Some lm.

Definition m_3sat_crit_lm : Prop :=
  exists lm, m_3sat_crit_opt = Some lm.

(** Lemmi di conferma decodifica *)
Lemma lm_3sat_easy_decodes :
  m_3sat_easy_lm.
Proof.
  unfold m_3sat_easy_lm, m_3sat_easy_opt.
  eexists; reflexivity.
Qed.

Lemma lm_3sat_crit_decodes :
  m_3sat_crit_lm.
Proof.
  unfold m_3sat_crit_lm, m_3sat_crit_opt.
  eexists; reflexivity.
Qed.

(** Versione forte: estrazione come valori espliciti *)
Definition m_3sat_easy_extracted : LMetrics :=
  match m_3sat_easy_opt with
  | Some lm => lm
  | None => default_lmetrics
  end.

Definition m_3sat_crit_extracted : LMetrics :=
  match m_3sat_crit_opt with
  | Some lm => lm
  | None => default_lmetrics
  end.

(** Predicati fase *)
Lemma lm_3sat_easy_subcrit :
  is_subcritical m_3sat_easy_extracted = true.
Proof. reflexivity. Qed.

Lemma lm_3sat_crit_critical :
  is_critical m_3sat_crit_extracted = true.
Proof. reflexivity. Qed.

(************************************************************************)
(* Fine V120 JSON->LMetrics bridge                                      *)
(************************************************************************)

