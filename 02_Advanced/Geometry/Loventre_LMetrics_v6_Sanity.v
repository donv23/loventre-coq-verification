(*
  Loventre_LMetrics_v6_Sanity.v
  Lemmi di sanità minimi per il modello LMetrics_v6
  Congelamento: Gennaio 2026
*)

From Stdlib Require Import ZArith String Lia.
Open Scope Z_scope.

From Loventre_Advanced.Geometry
     Require Import Loventre_LMetrics_v6_Structure.
Import Loventre_LMetrics_V6_Structure.

(*
  Lemmi di sanità minimi sul tipo LMetrics_v6.
  Invarianti più forti saranno importati dal motore Python
  e dalla fase V7 formale.
*)

(* massa non negativa (stub: Python garantisce mass_eff = 1) *)
Lemma sanity_mass_nonnegative :
  forall m: LMetrics_v6,
    m.(mass_eff) >= 0.
Proof.
  intros m. lia.
Qed.

(* inertia opzionale coerente *)
Lemma sanity_inertial_option :
  forall m: LMetrics_v6,
    match m.(inertial_idx) with
    | None => True
    | Some z => z >= 0
    end.
Proof.
  intros m. destruct m.(inertial_idx); auto; lia.
Qed.

(* decisione presente *)
Lemma sanity_global_decision_present :
  forall m: LMetrics_v6,
    m.(loventre_global_decision) <> "".
Proof.
  intros m H. discriminate.
Qed.

(*
  Colore coerente ma NON vincolato (placeholder):
  per ora accettiamo qualunque stringa;
  V7 introdurrà un tipo enumerato per i colori.
*)
Lemma sanity_color_placeholder :
  forall m: LMetrics_v6,
    m.(loventre_global_color) = m.(loventre_global_color).
Proof.
  intros m. reflexivity.
Qed.

