(*
  Loventre_Globalization_Structure.v

  FASE A — Struttura astratta di globalizzazione
  ----------------------------------------------

  Questo modulo collega:
  - strategie locali
  - famiglie di strategie
  - oggetti globali
  - coerenza globale

  Vincoli:
  - Nessuna costruzione Local → Global
  - Nessuna assunzione di esistenza
  - Nessuna GCT
  - Nessuna computazione o tempo
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import
  Loventre_Advanced.Geometry_Globalization.Loventre_Local_Strategy
  Loventre_Advanced.Geometry_Globalization.Loventre_Uniformity
  Loventre_Advanced.Geometry_Globalization.Loventre_Global_Coherence.

Section GlobalizationStructure.

  (*
    Una globalizzazione è semplicemente una funzione
    che associa a una famiglia di strategie
    un oggetto globale candidato.
  *)
  Definition Globalization :=
    (LocalStrategy -> Prop) -> GlobalObject.

  (*
    Una globalizzazione è ammissibile se,
    per ogni famiglia di strategie,
    l'oggetto globale prodotto è coerente
    rispetto a quella famiglia.
  *)
  Definition admissible_globalization
             (G : Globalization) : Prop :=
    forall F : LocalStrategy -> Prop,
      globally_coherent (G F) F.

End GlobalizationStructure.

