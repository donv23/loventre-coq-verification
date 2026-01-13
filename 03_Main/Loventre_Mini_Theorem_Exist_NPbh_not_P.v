(** Loventre_Mini_Theorem_Exist_NPbh_not_P.v
    Mini-teorema di esistenza:
    Esiste almeno una istanza NP-black-hole che NON è P-like,
    nel modello Loventre.
 *)

From Stdlib Require Import ZArith.

From Loventre_Core Require Import
  Loventre_Kernel
  Loventre_Foundation_Params.

From Loventre_Advanced Require Import
  Loventre_Tunneling_Model
  Loventre_Barrier_Model
  Loventre_Risk_Level
  Loventre_SAFE_Model
  Loventre_Class_Model
  Loventre_Risk_Level_Bridge
  Loventre_Class_Properties
  Loventre_Phase_Assembly
  Loventre_LMetrics_JSON_Witness.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Loventre_Geometry.

(** ----------------------------------------------------------- **)
(** TEOREMA MINI - CORE STATEMENT                               **)
(** ----------------------------------------------------------- **)

Theorem exists_NPbh_not_P :
  exists x : M,
      In_NPbh_Lov x /\
      ~ In_P_Lov x.
Proof.
  exists m_TSPcrit28_cli_demo.
  split.
  - apply m_TSPcrit28_is_NPbh.
  - intro HP.
    apply P_exclusive_NPbh with (x := m_TSPcrit28_cli_demo).
    + exact HP.
    + apply m_TSPcrit28_is_NPbh.
Qed.

