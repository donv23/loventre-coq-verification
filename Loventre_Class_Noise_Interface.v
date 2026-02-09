(**
  Loventre_Class_Noise_Interface.v
  dicembre 2025

  CANONICAL INTERFACE — BRIDGE ZERO

  Interfaccia semantica tra:
  - classi di complessità Loventre
  - ordine strutturale dei regimi di rumore

  Questo file NON introduce:
  - metriche
  - sensibilità
  - dinamica
  - probabilità
  - appartenenza puntuale

  Serve esclusivamente a congelare
  il significato strutturale delle classi.
*)

From Stdlib Require Import Reals.

Require Import Loventre_Noise_Regimes.
Require Import Loventre_Noise_Regimes_Order.
Require Import Loventre_Complexity_Noise_Classes.

(**
  Alias canonici del vocabolario (A11).
*)
Module NR := Loventre_Noise_Regimes.
Module NO := Loventre_Noise_Regimes_Order.
Module NC := Loventre_Complexity_Noise_Classes.

(**
  PRINCIPIO DI INTERFACCIA (CANON):

  Le classi di complessità Loventre
  NON sono primitive operative.

  Il loro significato strutturale è
  interamente determinato dal massimo
  regime di rumore ammissibile,
  tramite la funzione:

    max_noise_regime_of : Loventre_Class -> Noise_Regime
*)

(**
  Vincolo di non-ambiguità strutturale:

  Classi distinte DEVONO avere
  regimi massimi distinti.

  Questo è un vincolo di modello,
  non un teorema derivato.
*)
Axiom distinct_classes_have_distinct_noise_bounds :
  forall C1 C2 : NC.Loventre_Class,
    C1 <> C2 ->
    NC.max_noise_regime_of C1 <>
    NC.max_noise_regime_of C2.

(**
  Interpretazione canonica congelata:

  Una classe rappresenta una regione
  (iniziale) nell'ordine dei regimi di rumore.

  Nessuna nozione di appartenenza
  a metriche è introdotta qui.
*)

(**
  NOTA IMPORTANTE:

  Qualsiasi futura definizione di
  appartenenza di una metrica a una classe
  DEVE essere compatibile con questa interfaccia.

  In particolare:
  - non può ignorare i vincoli di rumore
  - non può contraddirli
  - non può ridefinire il significato delle classi
*)

