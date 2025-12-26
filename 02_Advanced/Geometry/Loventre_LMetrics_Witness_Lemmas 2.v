(** 
  Loventre LMetrics Witness – First Lemmas (Dicembre 2025)
  ========================================================

  Obiettivo:
    usare i witness CLI definiti in Loventre_LMetrics_Witness_CLI
    per dimostrare un primo mini–lemma strutturale:

      "se il GlobalDecision su m_seed11_safe è GD_safe,
       allora m_seed11_safe non è un Metrics_witness".

  Intuizione:
    - Metrics_witness m := SAT_crit m \/ TSP_crit m,
    - per i witness critici (TSP_crit28, SAT_crit16) ci aspettiamo GD_critical,
    - quindi un vero Metrics_witness deve avere GlobalDecision
      almeno BORDERLINE o CRITICAL, mai SAFE.
*)

From Loventre_Geometry Require Import Loventre_LMetrics_Witness_CLI.

Section CLI_Witness_First_Lemmas.

  Theorem seed11_safe_not_metrics_witness :
    loventre_global_decision m_seed11_safe = GD_safe ->
    ~ Metrics_witness m_seed11_safe.
  Proof.
    intros Hsafe Hwit.
    (* Dal testimone metrico otteniamo che il GlobalDecision
       deve essere BORDERLINE o CRITICAL (assioma globale). *)
    pose proof (witnesses_borderline_or_critical m_seed11_safe Hwit)
      as [Hb | Hc].
    - (* Caso 1: GD_borderline *)
      rewrite Hsafe in Hb.
      discriminate.
    - (* Caso 2: GD_critical *)
      rewrite Hsafe in Hc.
      discriminate.
  Qed.

End CLI_Witness_First_Lemmas.

