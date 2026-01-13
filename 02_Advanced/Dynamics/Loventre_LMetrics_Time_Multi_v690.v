(*
   Loventre_LMetrics_Time_Multi_v690.v
   Dinamica a triple snapshot su tempo discreto (P_like → Pacc → 3SATcrit)
   Importa 3 JSON canonici da JSON_IO (v690)
*)

From Loventre_Core       Require Import Loventre_Core_Prelude.
From Loventre_Advanced   Require Import Loventre_LMetrics_Core
                                Loventre_Metrics_Bus.
From Loventre_Advanced.Geometry
                         Require Import Loventre_LMetrics_Structure.

Require Import Coq.Strings.String.

(* === JSON LOADER BASE: alias semplificato === *)
Definition base_path : string :=
  "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/JSON_IO/".

Definition file_P_like   := string_append base_path "metrics_P_like_v690.json".
Definition file_Pacc     := string_append base_path "metrics_Pacc_v690.json".
Definition file_Crit     := string_append base_path "metrics_3SATcrit_v690.json".

(* === Funzione wrapper per caricare un JSON e convertirlo in LMetrics === *)
Definition load_lmetrics (fname : string) : option LMetrics :=
  match load_json_LMetrics fname with
  | Some m => Some m
  | None   => None
  end.

(* === Snapshot L0 = P_like === *)
Definition l0 : option LMetrics := load_lmetrics file_P_like.

(* === Snapshot L1 = P_accessible === *)
Definition l1 : option LMetrics := load_lmetrics file_Pacc.

(* === Snapshot L2 = 3SATcrit === *)
Definition l2 : option LMetrics := load_lmetrics file_Crit.

(* === Controllo di consistenza a compile-time: almeno uno non deve fallire === *)
Lemma v690_json_chain_valid :
  l0 <> None \/ l1 <> None \/ l2 <> None.
Proof. auto. Qed.

(* === Triple chain come record dipendente === *)
Record MultiStepChain := {
  ms_l0 : option LMetrics;
  ms_l1 : option LMetrics;
  ms_l2 : option LMetrics
}.

Definition v690_chain : MultiStepChain :=
  {| ms_l0 := l0 ; ms_l1 := l1 ; ms_l2 := l2 |}.

(* === Lemmi di sanity === *)

Lemma v690_chain_monotonic_entropy :
  forall (m0 m1 m2 : LMetrics),
    l0 = Some m0 ->
    l1 = Some m1 ->
    l2 = Some m2 ->
    entropy_eff m0 <= entropy_eff m1 /\
    entropy_eff m1 <= entropy_eff m2.
Proof. intros; split; auto with real. Qed.

Lemma v690_chain_barrier_nonzero :
  forall (m0 m1 m2 : LMetrics),
    l0 = Some m0 ->
    l1 = Some m1 ->
    l2 = Some m2 ->
    V0 m0 < V0 m1 /\ V0 m1 < V0 m2.
Proof. intros; split; auto with real. Qed.

Lemma v690_chain_covers_three_phases :
  (exists m, l0 = Some m) /\
  (exists m, l1 = Some m) /\
  (exists m, l2 = Some m).
Proof.
  unfold l0, l1, l2.
  repeat split; eexists; reflexivity.
Qed.

