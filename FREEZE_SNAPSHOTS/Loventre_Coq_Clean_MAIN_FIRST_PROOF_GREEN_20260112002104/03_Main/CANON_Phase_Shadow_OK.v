(**
  CANON_Phase_Shadow_OK.v

  CHECKPOINT FORMALE — 2025-12-28

  Questo file è una SENTINELLA di stabilità.

  Scopo:
  - Congelare lo stato VERDE del modulo SHADOW
    Loventre_LMetrics_Phase_CANON
  - Verificare che:
      * i predicati is_SAFE / is_WARNING / is_BLACKHOLE
        siano accessibili
      * i witness CANON esportati dal motore Python
        siano ancora ben tipati
      * i test minimi compilino

  Vincoli:
  - Nessuna definizione nuova
  - Nessun assioma
  - Nessuna prova
  - Nessuna importazione nel CANON principale
  - Nessuna modifica al Makefile

  Se questo file NON compila, qualcosa si è rotto.
*)

From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Phase_CANON_Index.

From Loventre_Main Require Import
  Test_CANON_Phase_Minimal.

(* ------------------------------------------------------------------ *)
(* SENTINELLA                                                         *)
(* ------------------------------------------------------------------ *)
(* Nessun contenuto: la compilazione è il test. *)

