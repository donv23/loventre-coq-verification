(*
  LAB-13.3 — Core_Global_Acyclic.v (v1 canonica, gennaio 2026)

  Versione POLIMORFA: Config e path sono parametri.
  Questo evita mismatch tra Core.Config e contromodelli concreti.

  Scopo del LAB-13.3:
  mostrare che una nozione debole di “acyclic” (assenza di self-loop)
  NON forza la rigidità globale rispetto a path.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Core_Global_Acyclic.

Context {Config : Type}.
Context (path : Config -> Config -> Prop).

(* Non-trivial one-step path *)
Definition nontrivial_path (x y : Config) : Prop :=
  x <> y /\ path x y.

(* Acyclic in senso debole: nessun self-loop *)
Definition Acyclic : Prop :=
  forall x : Config, ~ path x x.

(* Rigidità globale: nessun ritorno immediato su un edge non-triviale *)
Definition GlobalPathRigid : Prop :=
  forall x y : Config,
    nontrivial_path x y -> ~ path y x.

(* Claim da testare: Acyclic -> GlobalPathRigid *)
Definition Acyclic_Forces_GlobalPathRigid : Prop :=
  Acyclic -> GlobalPathRigid.

End Core_Global_Acyclic.
