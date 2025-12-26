(** Loventre_All.v
    Entry point unificato per il progetto Loventre_Coq_Clean.

    Questa versione unificata riesporta:
      - le fondazioni (01_Core) tramite Loventre_Foundation_All,
      - i moduli avanzati (02_Advanced) tramite Loventre_Advanced_All,
      - i moduli di alto livello (03_Main) tramite Loventre_Main_All
        (congettura, bridge TM–famiglie, blocco SAT_crit).
 *)

Require Export Loventre_Foundation_All.
Require Export Loventre_Advanced_All.
Require Export Loventre_Main_All.
Require Import Loventre_TSPcrit28_Witness.

