(**
  Loventre_LMetrics_Robustness.v
  dicembre 2025

  Predicati strutturali di robustezza su LMetrics.
  Formalizzazione Coq delle misure 1–3 del motore Python:

    (1) Stabilità strutturale
    (2) Blocco di fase / barriera
    (3) Invarianza

  Nessuna statistica.
  Nessun p-value.
*)

From Stdlib Require Import Reals.
Local Open Scope R_scope.

Require Import Loventre_LMetrics_Structure.

Module LMetrics_Robustness.

  Import Loventre_LMetrics.

  (**
    (1) Stabilità strutturale
    --------------------------------
    Una metrica è strutturalmente stabile se
    il suo potenziale informazionale è positivo
    (non degenerato).
  *)
  Definition is_structurally_stable (M : LMetrics) : Prop :=
    informational_potential M > 0.

  (**
    (2) Blocco di fase / barriera
    --------------------------------
    Esiste una barriera informazionale positiva
    che impedisce transizioni continue di regime.
  *)
  Definition is_phase_locked (M : LMetrics) : Prop :=
    V0 M > 0.

  (**
    (3) Invarianza
    --------------------------------
    L'orizzonte non è aperto (flag nullo),
    quindi il comportamento non dipende
    dalla rappresentazione locale.
  *)
  Definition is_invariant (M : LMetrics) : Prop :=
    horizon_flag M = 0.

  (**
    Aggregazione canonica
    --------------------------------
    Una metrica è canonicamente robusta
    se e solo se soddisfa tutte e tre le proprietà.
  *)
  Definition is_canonical_robust (M : LMetrics) : Prop :=
    is_structurally_stable M /\
    is_phase_locked M /\
    is_invariant M.

End LMetrics_Robustness.

