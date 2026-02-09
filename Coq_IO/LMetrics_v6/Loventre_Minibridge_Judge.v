From Stdlib Require Import Reals String.
From LMetrics_v6 Require Import LMetrics_v6_types.

(*
  Giudice Loventre Mini-Bridge 3SAT
  Classifica un witness JSON-generato in:
    - P_like (verde)
    - P_accessible (giallo)
    - NP_blackhole (rosso-nero)
*)

Inductive LClass :=
| P_like
| P_accessible
| NP_blackhole.

(* Regole di cutoff ispirate alle fasce v1206 *)
Definition classify (m : LMetrics) : LClass :=
  if Rlt_dec m.(risk_index) 0.30 then P_like
  else if Rlt_dec m.(risk_index) 0.60 then P_accessible
  else NP_blackhole.

(* Helper booleani *)
Definition is_P_like (m : LMetrics) : bool :=
  match classify m with
  | P_like => true | _ => false
  end.

Definition is_P_accessible (m : LMetrics) : bool :=
  match classify m with
  | P_accessible => true | _ => false
  end.

Definition is_NP_blackhole (m : LMetrics) : bool :=
  match classify m with
  | NP_blackhole => true | _ => false
  end.

