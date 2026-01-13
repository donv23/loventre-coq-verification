(**
  Loventre_Main_Theorem_v8_Interface.v
  V8 – Post-Freeze January 2026
  ----------------------------------------------------
  Questo file costituisce l'interfaccia principale V8
  che rende visibili i witness V7 nel nuovo ramo V8.

  Obiettivi:
  - Importare la Prelude V8 (accesso ai moduli V7)
  - Importare il pacchetto witness V7
  - Importare gli alias V8
  - Riesportare tutto per i file Mini, Test e All
*)

From Loventre_Main Require Import
     Loventre_Main_Theorem_v8_Prelude.

From Loventre_Advanced.Geometry Require Import
     Loventre_LMetrics_v7_Witness_Package.

From Loventre_Main Require Import
     Loventre_LMetrics_v8_Aliases.

Export Loventre_LMetrics_v7_Witness_Package.
Export Loventre_LMetrics_v8_Aliases.

(** Nessuna logica aggiuntiva.
    Nessun lemma, nessun predicato.
    Questo modulo serve solo a esporre
    i testimoni e gli alias al ramo V8.
*)

(* Fine file Interface V8 *)

