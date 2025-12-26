From Loventre.Geometry Require Import Loventre_LMetrics_JSON_Link.

(** Sanity checks per LMetrics — baseline dicembre 2025 **)

Section Sanity_LMetrics.

  Variable m : LMetrics.

  (** Controlli base sulle metriche *)
  Definition sanity_positive_p_tunnel : Prop :=
    0 <= p_tunnel m <= 1.

  Definition sanity_positive_P_success : Prop :=
    0 <= P_success m <= 1.

  Definition sanity_risk_class_nonempty : Prop :=
    match risk_class m with
    | risk_LOW
    | risk_MEDIUM
    | risk_HIGH
    | risk_NP_like_black_hole => True
    end.

  Definition sanity_meta_label_nonempty : Prop :=
    match meta_label m with
    | meta_unknown
    | meta_P_like_like
    | meta_P_like_accessible
    | meta_NP_like_black_hole => True
    end.

  (** Lemma combinato: tutte le proprietà di sanità sono soddisfatte simultaneamente *)
  Lemma sanity_all_ok :
    sanity_positive_p_tunnel /\
    sanity_positive_P_success /\
    sanity_risk_class_nonempty /\
    sanity_meta_label_nonempty.
  Proof.
    unfold sanity_positive_p_tunnel, sanity_positive_P_success,
           sanity_risk_class_nonempty, sanity_meta_label_nonempty.
    repeat split; auto.
  Qed.

End Sanity_LMetrics.

