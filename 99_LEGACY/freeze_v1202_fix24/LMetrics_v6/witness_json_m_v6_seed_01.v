
(** Auto-generated SAFE-aware witness: m_v6_seed_01 *)
From Stdlib Require Import Reals.
From Stdlib Require Import String.
From LMetrics_v6 Require Import LMetrics_v6_types.

Definition m_v6_seed_01_example : LMetrics :=
  mkLMetrics
    0.1%R
    0.2%R
    0.3%R
    0.4%R
    0.5%R
    LOW
    SAFE
    GREEN
    0.6%R
    1
    "m_v6_seed_01"%string.
