(** Loventre_Main_Theorem_v3_Annotated.v
    Versione annotata del primo teorema principale (beta)
    per il modello Loventre v3.

    LOGICA:
      (1) Nessun P-like può essere NP-black-hole
      (2) Esiste almeno un NP-black-hole non P-like
      ------------------------------------------------
      ⇒ Le classi sono logicamente separate nel modello.

    NOTE:
      - Questa non è una prova di P≠NP classico.
      - Il risultato è interno al modello Loventre v3.
      - La separazione è logica, non computazionale.
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
(** Teorema Principale Annotato (Loventre v3)                *)
(** ========================================================= *)

Theorem Loventre_Separation_P_vs_NPbh_Annotated :
  (forall x, In_P_Lov x -> ~ In_NPbh_Lov x) /\
  (exists y, In_NPbh_Lov y /\ ~ In_P_Lov y).
Proof.
  (** Prima componente: ogni P-like non può essere NP-black-hole *)
  split.
  - apply P_not_NPbh.

  (** Seconda componente: esistenza di un NP-black-hole non P-like *)
  - apply exists_NPbh_not_P.
Qed.

