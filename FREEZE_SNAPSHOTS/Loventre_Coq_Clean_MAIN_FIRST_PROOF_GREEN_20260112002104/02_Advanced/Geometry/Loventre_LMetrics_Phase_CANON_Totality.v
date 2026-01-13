(**
  Loventre_LMetrics_Phase_CANON_Totality.v

  Lemma di totalità per la semantica CANON.

  Ogni LMetrics cade in una delle tre classi:
    SAFE / WARNING / BLACKHOLE

  - solo logica proposizionale
  - nessuna aritmetica
  - nessuna tattica non standard
  - compatibile Coq 8.18

  Dicembre 2025
*)

From Stdlib Require Import Classical_Prop.

From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Phase_CANON.

Import Loventre_LMetrics_Phase_CANON.

Lemma CANON_totality :
  forall m,
    is_SAFE m \/ is_WARNING m \/ is_BLACKHOLE m.
Proof.
  intro m.
  unfold is_WARNING.
  destruct (classic (is_SAFE m)) as [Hsafe | Hnotsafe].
  - left; exact Hsafe.
  - right.
    destruct (classic (is_BLACKHOLE m)) as [Hbh | Hnotbh].
    + right; exact Hbh.
    + left; split; assumption.
Qed.

