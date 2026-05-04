(*
  Loventre_Global_Coherence.v

  FASE A — Coerenza globale (astratta)
  -----------------------------------

  Questo modulo introduce il concetto astratto di coerenza globale.

  Vincoli:
  - Nessuna costruzione Local → Global
  - Nessuna GCT
  - Nessuna computazione o tempo
  - Nessuna assunzione di esistenza
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import
  Loventre_Advanced.Geometry_Globalization.Loventre_Local_Strategy.

Section GlobalCoherence.

  (*
    Un oggetto globale astratto.
    Non è costruito, non è derivato:
    è solo un tipo.
  *)
  Parameter GlobalObject : Type.

  (*
    Relazione di compatibilità tra un oggetto globale
    e una strategia locale.
  *)
  Parameter compatible :
    GlobalObject -> LocalStrategy -> Prop.

  (*
    Coerenza globale:
    un oggetto globale è coerente rispetto
    a una famiglia astratta di strategie locali.
    (La famiglia è vista come un predicato.)
  *)
  Definition globally_coherent
             (G : GlobalObject)
             (F : LocalStrategy -> Prop) : Prop :=
    forall s : LocalStrategy, F s -> compatible G s.

End GlobalCoherence.

