(** Loventre_TSPcrit28_Witness.v
    Mini seed Coq – Witness LMetrics derivati dal motore Python (dicembre 2025)

    Versione astratta:
    - non usiamo la notazione di record per LMetrics,
    - fissiamo solo l’esistenza di due stati BusState che sono witness
      per TSP_crit e SAT_crit e quindi per Metrics_witness.
*)

Require Import Loventre_SAT_TSP_Critical_Metrics.

(** ------------------------------------------------------------------ *)
(** 1. Witness astratti come stati del bus                             *)
(** ------------------------------------------------------------------ *)

Parameter m_TSPcrit28 : BusState.
Parameter m_SATcrit16 : BusState.

(** m_TSPcrit28: witness per una istanza TSP_crit_28 NP_like_black_hole. *)
Axiom m_TSPcrit28_is_witness :
  TSP_crit m_TSPcrit28 /\ Metrics_witness m_TSPcrit28.

(** m_SATcrit16: witness per una istanza SAT_crit_16 NP_like_black_hole. *)
Axiom m_SATcrit16_is_witness :
  SAT_crit m_SATcrit16 /\ Metrics_witness m_SATcrit16.

(** ------------------------------------------------------------------ *)
(** 2. Lemmi di proiezione (comodi per gli usi successivi)             *)
(** ------------------------------------------------------------------ *)

Lemma m_TSPcrit28_TSP_crit :
  TSP_crit m_TSPcrit28.
Proof.
  destruct m_TSPcrit28_is_witness as [H _]; exact H.
Qed.

Lemma m_TSPcrit28_Metrics_witness :
  Metrics_witness m_TSPcrit28.
Proof.
  destruct m_TSPcrit28_is_witness as [_ H]; exact H.
Qed.

Lemma m_SATcrit16_SAT_crit :
  SAT_crit m_SATcrit16.
Proof.
  destruct m_SATcrit16_is_witness as [H _]; exact H.
Qed.

Lemma m_SATcrit16_Metrics_witness :
  Metrics_witness m_SATcrit16.
Proof.
  destruct m_SATcrit16_is_witness as [_ H]; exact H.
Qed.

Section Consequences_of_Conjecture.

  Hypothesis H_conj :
    witness_globally_borderline_or_critical.

  Lemma m_TSPcrit28_global_borderline_or_critical :
    loventre_global_decision m_TSPcrit28 = GD_borderline \/
    loventre_global_decision m_TSPcrit28 = GD_critical.
  Proof.
    apply H_conj.
    apply m_TSPcrit28_Metrics_witness.
  Qed.

  Lemma m_SATcrit16_global_borderline_or_critical :
    loventre_global_decision m_SATcrit16 = GD_borderline \/
    loventre_global_decision m_SATcrit16 = GD_critical.
  Proof.
    apply H_conj.
    apply m_SATcrit16_Metrics_witness.
  Qed.

End Consequences_of_Conjecture.

