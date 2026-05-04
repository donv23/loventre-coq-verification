(** SAFE_Barrier_Structure.v — versione v5.2 pulita e tipata *)

From Coq Require Import Reals.
Local Open Scope R_scope.

Record SAFE_Barrier_Structure := {
  barrier_V0 : R
}.

(***********************************************************)
(*                Predicati SAFE / BLACKHOLE               *)
(***********************************************************)

Definition is_SAFE_barrier (B : SAFE_Barrier_Structure) : Prop :=
  barrier_V0 B = 0%R.

Definition is_BLACKHOLE_barrier (B : SAFE_Barrier_Structure) : Prop :=
  barrier_V0 B <> 0%R.

(***********************************************************)
(*                Lemma: esclusione                        *)
(***********************************************************)

Lemma safe_or_blackhole_exclusion :
  forall B : SAFE_Barrier_Structure,
    is_SAFE_barrier B \/ is_BLACKHOLE_barrier B.
Proof.
  intros B.
  unfold is_SAFE_barrier, is_BLACKHOLE_barrier.
  destruct (Req_dec (barrier_V0 B) 0%R) as [H | H].
  - left; exact H.
  - right; exact H.
Qed.

(***********************************************************)
(*                Parametri v5.2                           *)
(*   IMPORTANTISSIMO: dichiarati come reali               *)
(***********************************************************)

Parameter informational_threshold_safe : R.
Parameter informational_threshold_crit : R.

Axiom informational_threshold_order :
  informational_threshold_safe < informational_threshold_crit.

