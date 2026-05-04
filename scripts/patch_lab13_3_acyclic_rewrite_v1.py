from pathlib import Path

ROOT = Path("/Users/vincenzoloventre/Desktop/loventre-coq-cycle11-lab")

core_path = ROOT / "02_Advanced/LAB_13_Global_Rigidity/L13_3_Acyclic/Core/Core_Global_Acyclic.v"
cm_path   = ROOT / "02_Advanced/LAB_13_Global_Rigidity/L13_3_Acyclic/CounterModel/CounterModel_Global_Acyclic.v"

core_txt = r'''(*
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
'''

cm_txt = r'''(*
  LAB-13.3 — CounterModel_Global_Acyclic.v (v1 canonica, gennaio 2026)

  Contromodello: Acyclic (no self-loop) può valere,
  ma GlobalPathRigid può fallire (2-cycle a<->b).

  Questo nega: Acyclic -> GlobalPathRigid.
*)

Require Import
  Loventre_Advanced.LAB_13_Global_Rigidity.L13_3_Acyclic.Core.Core_Global_Acyclic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* === Configurazioni concrete === *)

Inductive Config : Type :=
| a
| b
| c.

(* === Relazione path (con 2-cycle a<->b, nessun self-loop) === *)

Inductive path : Config -> Config -> Prop :=
| p_ab : path a b
| p_ba : path b a
| p_bc : path b c.

(* === Lemmi base di disequazione === *)

Lemma a_neq_b : a <> b. Proof. discriminate. Qed.
Lemma b_neq_a : b <> a. Proof. discriminate. Qed.

(* === Acyclic (debole) vale: nessun path x x === *)

Lemma Acyclic_holds :
  Core_Global_Acyclic.Acyclic (Config:=Config) path.
Proof.
  unfold Core_Global_Acyclic.Acyclic.
  intros x Hxx.
  inversion Hxx.
Qed.

(* === GlobalPathRigid fallisce (per a<->b) === *)

Lemma not_GlobalPathRigid :
  ~ Core_Global_Acyclic.GlobalPathRigid (Config:=Config) path.
Proof.
  unfold Core_Global_Acyclic.GlobalPathRigid.
  intro H.
  specialize (H a b).
  assert (Core_Global_Acyclic.nontrivial_path (Config:=Config) path a b) as Hnt.
  { unfold Core_Global_Acyclic.nontrivial_path. split.
    - exact a_neq_b.
    - exact p_ab.
  }
  (* H dice: non può valere path b a, ma noi abbiamo p_ba *)
  exact (H Hnt p_ba).
Qed.

(* === Quindi: Acyclic non forza GlobalPathRigid === *)

Lemma not_Acyclic_Forces_GlobalPathRigid :
  ~ Core_Global_Acyclic.Acyclic_Forces_GlobalPathRigid (Config:=Config) path.
Proof.
  unfold Core_Global_Acyclic.Acyclic_Forces_GlobalPathRigid.
  intro H.
  apply not_GlobalPathRigid.
  apply H.
  exact Acyclic_holds.
Qed.
'''

core_path.parent.mkdir(parents=True, exist_ok=True)
cm_path.parent.mkdir(parents=True, exist_ok=True)

core_path.write_text(core_txt, encoding="utf-8")
cm_path.write_text(cm_txt, encoding="utf-8")

print("OK: riscritti Core_Global_Acyclic.v e CounterModel_Global_Acyclic.v (LAB-13.3, v1 canonica).")

