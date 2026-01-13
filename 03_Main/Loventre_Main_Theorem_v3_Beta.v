(** Loventre_Main_Theorem_v3_Beta.v
    Primo teorema principale (beta) del modello Loventre v3.

    Se:
      (1) Nessuna istanza P-like può essere NP-black-hole
      (2) Esiste almeno una istanza NP-black-hole non P-like

    Allora:
      Le due classi sono logicamente separate nel modello Loventre v3.
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
  Loventre_Phase_Assembly.

From Loventre_Main Require Import
  Loventre_Mini_Theorem_P_vs_NPbh
  Loventre_Mini_Theorem_Exist_NPbh_not_P.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Loventre_Geometry.

(** ========================================================= *)
(** Teorema Principale (beta) v3                             *)
(** ========================================================= *)

Theorem Loventre_Separation_P_vs_NPbh :
  (forall x, In_P_Lov x -> ~ In_NPbh_Lov x) /\
  (exists y, In_NPbh_Lov y /\ ~ In_P_Lov y).
Proof.
  split.
  - apply P_not_NPbh.
  - apply exists_NPbh_not_P.
Qed.

