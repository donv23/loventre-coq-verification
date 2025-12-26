(** Loventre_Main_Index.v
    Entry-point CANON del livello Main del modello Loventre.

    Questo file importa esclusivamente:
    - Core
    - Advanced (via indice)
    ed è il punto di partenza per i teoremi globali.
*)

From Loventre_Core Require Import
  Loventre_Kernel
  Loventre_Foundation_Types
  Loventre_Foundation_Params
  Loventre_Foundation_Entropy.

From Loventre_Advanced Require Import
  Loventre_Advanced_Index.

