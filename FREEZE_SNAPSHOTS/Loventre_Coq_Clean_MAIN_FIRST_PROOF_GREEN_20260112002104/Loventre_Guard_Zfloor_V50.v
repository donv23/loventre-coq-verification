(** Loventre_Guard_Zfloor_V50.v
    Guardiano CORE V50 per Zfloor — gennaio 2026
    Scopo: semplicemente compilare e forzare coerenza tra:
      - Loventre_Zfloor_Core
      - Loventre_Zfloor_Lemmas
      - Loventre_Zfloor_Mono
      - Loventre_Zfloor_Compat
      - Loventre_Zfloor_Compat_RNZ
      - Loventre_Zfloor_Migrate_Core

    Nessuna prova nuova. Solo Require.
 *)

From Stdlib Require Import Reals ZArith Zfloor Psatz.

From Loventre_Core Require Import
     Loventre_Zfloor_Core
     Loventre_Zfloor_Lemmas
     Loventre_Zfloor_Mono
     Loventre_Zfloor_Compat
     Loventre_Zfloor_Compat_RNZ
     Loventre_Zfloor_Migrate_Core.

(* Dummy lemma to ensure everything links in V50 *)
Lemma loventre_guard_zfloor_compiles :
  True.
Proof. exact I. Qed.

