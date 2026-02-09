From Stdlib Require Import ZArith QArith String Lists.List.
Import ListNotations.

Open Scope Z_scope.
Open Scope Q_scope.

(* Conversioni semplici da interi Python a Z/Q *)
Definition z_of_int (n : Z) : Z := n.

Definition q_of_int (n : Z) : Q := inject_Z n.

(* Divisione sicura con conversione Z→Q *)
Definition q_div (num den : Z) : Q :=
  if Z.eq_dec den 0 then inject_Z 0 else (inject_Z num) / (inject_Z den).

