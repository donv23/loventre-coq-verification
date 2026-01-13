(**
  ZZ_Zfloor_Inspect.v
  Rocq 9.1 — Zfloor/Zceil/archimed discovery
  Nessun lemma, solo check e search
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Rdefinitions Rbasic_fun.
From Stdlib Require Import ZArith.
From Stdlib Require Import Zfloor.
From Stdlib Require Import Lia Psatz.

Open Scope R_scope.
Open Scope Z_scope.

(* 1. Verifica che archimed sia disponibile *)
Check archimed.

(* 2. Che cosa sa Rocq su floor/down/up *)
Search Zfloor.
Search (up _).
Search (down _).
Search (IZR _ <= _).
Search (_ < IZR _).
Search (_ <= IZR _).
Search (_ < _ + 1).

(* 3. Mostra le firme delle funzioni *)
Check Zfloor.
Check up.
Check down.
Check IZR.

(* 4. Esplora interazioni possibili *)
SearchRewrite (IZR ?z).
SearchRewrite (up ?x - 1).

(* 5. Se compare qualsiasi errore → fermarci *)

