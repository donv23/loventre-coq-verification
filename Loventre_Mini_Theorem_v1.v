(**
  Loventre_Mini_Theorem_v1.v
  dicembre 2025

  MINI-THEOREM CANONICO — v1

  Prima separazione strutturale non banale
  nel modello di complessità Loventre.

  Nessuna dinamica.
  Nessuna probabilità.
  Nessun claim P≠NP classico.
*)

From Stdlib Require Import Reals.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_Complexity_Noise_Classes.
Require Import Loventre_Structural_Class_Separation_CANON.

Module Loventre_Mini_Theorem_v1.

  Import Loventre_LMetrics.

  (**
    Mini-Theorem Loventre v1:

    Nel modello Loventre esiste almeno una metrica
    che NON appartiene alla classe P_STR.

    Questo è conseguenza diretta della
    separazione strutturale canonica.
  *)
  Theorem Loventre_Mini_Theorem_v1 :
    exists M : LMetrics,
      ~ Loventre_Sensitivity_Excludes_PSTR_Class.belongs_to_class
          M
          Loventre_Complexity_Noise_Classes.P_STR.
  Proof.
    apply
      Loventre_Structural_Class_Separation_CANON
        .exists_non_PSTR_metric.
  Qed.

End Loventre_Mini_Theorem_v1.

