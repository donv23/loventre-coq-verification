(*
  Loventre_Main_Theorem_V1000.v
  Versione: V1000 — Teorema Principale Loventre v1
  Obiettivo:
    Formalizzare nel modello Loventre
    la separazione interna tra classi informazionali:

      esiste un witness computazionale reale
      (derivato dal motore Python → JSON → Coq)
      tale che:
         - è NP_blackhole
         - non è P_like
         - non è P_accessible
         - e resta NP_blackhole per tutta l’evoluzione

    Questo teorema chiude la versione 1.
    Nessun Admitted. Nessun assioma aggiuntivo.
*)

From Coq Require Import Reals Lia.

From Loventre_Core Require Import Loventre_Prelude.
From Loventre_Core Require Import Loventre_LMetrics_Core.

From Loventre_Advanced Require Import Loventre_LMetrics_JSON_Witness.
From Loventre_Advanced Require Import Loventre_3SATcrit_NoAdmit_V920.
From Loventre_Advanced Require Import Loventre_3SATcrit_Stability_V950.
From Loventre_Advanced Require Import Loventre_Class_Model.
From Loventre_Advanced Require Import Loventre_Class_Dynamics_Bridge_V850.
From Loventre_Main     Require Import Loventre_Mini_Theorem_V980.

Open Scope R_scope.

Module Loventre_Main_Theorem_V1000.

  (** Richiamiamo il witness già esistente *)
  Definition witness := Loventre_Mini_Theorem_V980.witness.

  (**
     Teorema principale:
     Esiste almeno un w computazionale
     che appartiene a NP_blackhole
     e non appartiene a P_like
     e nemmeno a P_accessible
   *)
  Theorem Loventre_Main_Theorem_v1 :
    exists w,
        is_NP_blackhole w
      /\ ~ is_P_like w
      /\ ~ is_P_accessible w.
  Proof.
    exact Loventre_Mini_Theorem_V980.Loventre_internal_separation_mini.
  Qed.

  (**
     Corollario dinamico (forma estesa):
     Per tale witness, per ogni passo di evoluzione
     resta in NP_blackhole
   *)
  Corollary Loventre_Main_Theorem_v1_dynamic :
    forall n,
      is_NP_blackhole (evolve_n n witness).
  Proof.
    intro n.
    apply Loventre_3SATcrit_Stability_V950.threeSATcrit_forever_NP_blackhole.
  Qed.

End Loventre_Main_Theorem_V1000.

