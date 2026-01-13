(**
  Loventre_Main_2SAT_Citable_Theorem.v
  V96 — Teorema Citabile (Index)

  Questo file NON introduce nuovi lemmi
  e NON modifica nulla in Geometry/Class/Core.

  Funzione:
    • Rende citabili i risultati ottenuti su 2-SAT
    • Re-esporta i moduli contenenti le prove effettive
    • Punto di ingresso pubblico e pulito per articoli/paper

  Nessun Axiom. Nessun Admitted. Nessuna prova nuova.
*)

From Loventre_Core       Require Export Loventre_Core_Prelude.
From Loventre_Advanced   Require Export Loventre_LMetrics_Core.
From Loventre_Advanced   Require Export Loventre_Metrics_Bus.

From Loventre_Advanced   Require Export Loventre_Class_Model.
From Loventre_Advanced   Require Export Loventre_Phase_Assembly.
From Loventre_Advanced   Require Export Loventre_SAFE_Model.
From Loventre_Advanced   Require Export Loventre_Class_Properties.

(** Importa e rende citabili i tre pilastri conclusivi del ciclo 2-SAT *)
From Loventre_Main       Require Export Loventre_Main_2SAT_Separation.
From Loventre_Main       Require Export Loventre_Main_2SAT_Global_Structural_Theorem.
From Loventre_Main       Require Export Loventre_Main_2SAT_Validation_Chain.

(** Punto unico di riferimento esterno *)
Module Loventre_2SAT_Citable_Theorem.
  (**
    Da qui un eventuale paper può importare:

      From Loventre_Main Require Import Loventre_Main_2SAT_Citable_Theorem.

    e avere immediatamente accesso a:
      • la separazione easy/critico
      • la classificazione Pacc/Safe/NPbh
      • la validazione della pipeline
  *)
End Loventre_2SAT_Citable_Theorem.

