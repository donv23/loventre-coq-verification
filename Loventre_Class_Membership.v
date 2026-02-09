(**
  Loventre_Class_Membership.v
  dicembre 2025

  CANON — Bridge strutturale di appartenenza

  Scopo:
  fornire un'interfaccia canonica e minimale
  che collega LMetrics alle classi di complessità
  tramite vincoli di rumore, SENZA dinamica.

  Nessuna probabilità.
  Nessuna perturbazione.
  Nessuna costruzione operativa.
*)

From Stdlib Require Import Reals.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_Noise_Regimes.
Require Import Loventre_Complexity_Noise_Classes.

(**
  Alias canonici del vocabolario (A11)
*)
Module LM := Loventre_LMetrics.
Module NR := Loventre_Noise_Regimes.
Module NC := Loventre_Complexity_Noise_Classes.

(**
  Predicato canonico di appartenenza
  (astratto, ma unico nel progetto).
*)
Parameter belongs_to_class :
  LM.LMetrics ->
  NC.Loventre_Class ->
  Prop.

(**
  Assioma di coerenza strutturale (⇒):

  Se una metrica appartiene a una classe,
  allora NON ammette regimi di rumore
  incompatibili con quella classe.
*)
Axiom membership_respects_noise :
  forall (M : LM.LMetrics) (C : NC.Loventre_Class),
    belongs_to_class M C ->
    forall r : NR.Noise_Regime,
      ~ (
        NC.respects_noise_class C r = False
      ).

(**
  Assioma di completezza strutturale minimale (⇐):

  Se una metrica NON viola i vincoli
  di rumore di una classe,
  allora può appartenere a quella classe.

  Questo assioma NON è costruttivo:
  serve solo a evitare un bridge vuoto.
*)
Axiom noise_respecting_implies_membership :
  forall (M : LM.LMetrics) (C : NC.Loventre_Class),
    (forall r : NR.Noise_Regime,
       NC.respects_noise_class C r \/ r = NC.max_noise_regime_of C) ->
    belongs_to_class M C.

