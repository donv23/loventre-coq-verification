(*
  Loventre_3SAT_Class_Local_v107.v
  --------------------------------
  Primo collegamento di 3SAT con le classi informazionali nel modello Loventre.

  Obiettivo di questo step:
    - Collocare l’istanza 3SAT valutata in SAFE (v105)
      dentro la tassonomia locale delle classi informazionali.
    - Nessun claim globale, nessun bridge Main, nessun assioma nuovo.
    - Solo classificazione locale “P-like / accessibile / critica / BH-like”
      secondo horizon_flag + SAFE.

  Status:
    - Tutto locale e sperimentale.
    - Nessun impatto su 2SAT né Phase Assembly.
*)

From Loventre_Core      Require Import Loventre_Core_Prelude.
From Loventre_Advanced   Require Import
     Loventre_LMetrics_Core
     Loventre_Metrics_Bus
     Loventre_Class_Model
     Loventre_SAFE_Model.
From Loventre_Advanced.Geometry Require Import
     Loventre_3SAT_Decode_Compute_v104
     Loventre_3SAT_SAFE_Local_v105.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Loventre_3SAT_Class_Local_v107.

  (** Classificazione locale:
      Usiamo la SAFE locale calcolata in v105 e
      horizon_flag fornito da decode/compute v104.
  *)

  Definition in_P_like_local (m : LMetrics) : Prop :=
    (horizon_flag m = false) /\ (is_SAFE_local_3SAT m = true).

  Definition in_NP_bh_like_local (m : LMetrics) : Prop :=
    (horizon_flag m = true) /\ (is_SAFE_local_3SAT m = false).

  Definition in_boundary_local (m : LMetrics) : Prop :=
    horizon_flag m = true /\ is_SAFE_local_3SAT m = true.

  (** Osservazione:
      boundary_local è la regione grigia: 3SAT “critico ma trattenuto”.
  *)

  Lemma P_like_implies_not_bh_local :
    forall m, in_P_like_local m -> ~ in_NP_bh_like_local m.
  Proof.
    intros m [Hh Hs].
    unfold in_NP_bh_like_local.
    intros [Hh' Hs'].
    rewrite Hh in Hh'. discriminate.
  Qed.

  (** Placeholder per futura relazione con Class_Model completo. *)
  Conjecture local_class_respects_global_hints :
    forall m,
      in_P_like_local m \/ in_boundary_local m \/ in_NP_bh_like_local m.

End Loventre_3SAT_Class_Local_v107.

