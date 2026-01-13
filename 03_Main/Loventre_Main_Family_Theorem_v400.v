(**
  ------------------------------------------------------------
   Loventre_Main_Family_Theorem_v400.v
   MAIN THEOREM aggregato per la famiglia 2SAT/3SAT
   Dicembre 2026 — V400
  ------------------------------------------------------------
*)

From Loventre_Core Require Import
  Loventre_Core_Prelude
  Loventre_Foundation_Types
  Loventre_Foundation_Params
  Loventre_Foundation_Entropy.

From Loventre_Advanced Require Import
  Loventre_LMetrics_Core
  Loventre_Metrics_Bus
  Loventre_Class_Model
  Loventre_Class_Properties
  Loventre_Phase_Assembly
  Loventre_SAFE_Model.

From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_Structure
  Loventre_2SAT_EasyCrit_Compare
  Loventre_2SAT_Decode_Compute
  Loventre_Test_Pacc_2SAT_Profile_v3
  Loventre_Test_All_2SAT
  Loventre_3SAT_BH_Local_v110
  Loventre_2SAT3SAT_Mini_Theorem_v160
  Loventre_Family_SAFE_Bridge_v330
  Loventre_Family_UNSAFE_Bridge_v340.

Set Implicit Arguments.
Set Asymmetric Patterns.

(** -------------------------------------------------------- **)
(** 1) Dominio della famiglia 2SAT/3SAT                     **)
(** -------------------------------------------------------- **)

Definition In_Family_2SAT3SAT (M : LMetrics) : Prop :=
  In_2SAT_domain M \/ In_3SAT_domain M.

(** -------------------------------------------------------- **)
(** 2) Safe <-> Pacc equivalenza globale                     **)
(** -------------------------------------------------------- **)

Theorem Loventre_Family_Safe_Pacc_v400 :
  forall M,
    In_Family_2SAT3SAT M ->
    SAFE M <-> In_Pacc_Lov M.
Proof.
  intros M HF.
  unfold In_Family_2SAT3SAT in HF.
  destruct HF as [H2 | H3].

  - (** Caso 2SAT **)
    apply Family_SAFE_for_2SAT; assumption.

  - (** Caso 3SAT **)
    apply Family_SAFE_for_3SAT; assumption.
Qed.

(** -------------------------------------------------------- **)
(** 3) Gap strutturale: esiste M NON SAFE nella famiglia      **)
(** -------------------------------------------------------- **)

Theorem Loventre_Family_Unsafe_Exists_v400 :
  exists M, In_Family_2SAT3SAT M /\ ~ SAFE M.
Proof.
  refine (_).
  (** Dal bridge UNSAFE abbiamo almeno un 3SAT critico *)
  destruct Family_UNSAFE_exists as [M HM].
  exists M; destruct HM as [Hfam Huns].
  split; auto.
Qed.

(** -------------------------------------------------------- **)
(** 4) Gap di classe: NPblackhole ≠ Pacc nella famiglia       **)
(** -------------------------------------------------------- **)

Theorem Loventre_Family_Class_Gap_v400 :
  exists M N,
    In_Family_2SAT3SAT M /\
    In_Pacc_Lov M /\
    In_Family_2SAT3SAT N /\
    In_NPblackhole_Lov N.
Proof.
  (** Estraggo direttamente dal mini teorema famiglia *)
  refine _.
  exact Family_mini_gap_2SAT3SAT.
Qed.

(** -------------------------------------------------------- **)
(** 5) Main theorem aggregato                                **)
(** -------------------------------------------------------- **)

Theorem Loventre_Family_Main_v400 :
  (forall M, In_Family_2SAT3SAT M ->
        SAFE M <-> In_Pacc_Lov M)
  /\ (exists M, In_Family_2SAT3SAT M /\ ~ SAFE M)
  /\ (exists M N,
        In_Family_2SAT3SAT M /\
        In_Pacc_Lov M /\
        In_Family_2SAT3SAT N /\
        In_NPblackhole_Lov N).
Proof.
  repeat split.
  - apply Loventre_Family_Safe_Pacc_v400.
  - apply Loventre_Family_Unsafe_Exists_v400.
  - apply Loventre_Family_Class_Gap_v400.
Qed.

