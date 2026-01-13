(** Loventre_Test_All.v
    Entry point di test per Loventre v3
    Compila tutti i componenti CORE+ADV+MAIN in un solo colpo.

    Questo file non dimostra nulla di nuovo:
    - importa l'intero stack
    - garantisce che non ci siano buchi di dipendenza
    - è usato per validazione “green state”
*)

From Stdlib Require Import ZArith.

From Loventre_Core Require Import
  Loventre_Core_Prelude
  Loventre_Kernel
  Loventre_Foundation_Types
  Loventre_Foundation_Params
  Loventre_Foundation_Entropy.

From Loventre_Advanced Require Import
  Loventre_Curvature_Field
  Loventre_Potential_Field
  Loventre_Barrier_Model
  Loventre_Tunneling_Model
  Loventre_Risk_Level
  Loventre_Risk_From_Tunneling
  Loventre_Risk_Level_Bridge
  Loventre_SAFE_Model
  Loventre_Class_Model
  Loventre_Class_Properties
  Loventre_Phase_Assembly.

From Loventre_Main Require Import
  Loventre_Mini_Theorem_P_vs_NPbh
  Loventre_Mini_Theorem_Exist_NPbh_not_P
  Loventre_Main_Theorem_v3_Beta
  Loventre_Main_Theorem_v3_Annotated.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Loventre_Geometry.

(* Dummy goal to force full linking *)
Goal True. exact I. Qed.

