(* ======================================================= *)
(* Formal_Core_Sig.v                                       *)
(* Firma astratta del core (D2 istanziabile)               *)
(* ======================================================= *)

Module Type FORMAL_CORE.

  (* Oggetti e morfismi *)
  Parameter Obj : Type.
  Parameter Mor : Obj -> Obj -> Type.

  Parameter id :
    forall X : Obj, Mor X X.

  Parameter comp :
    forall {X Y Z : Obj}, Mor X Y -> Mor Y Z -> Mor X Z.

  (* Configurazioni *)
  Parameter Config : Obj -> Type.

  (* Funtore delle configurazioni *)
  Parameter S_map :
    forall {X Y : Obj}, Mor X Y -> Config X -> Config Y.

  Axiom S_id :
    forall (X : Obj) (c : Config X),
      S_map (id X) c = c.

  Axiom S_comp :
    forall (X Y Z : Obj)
           (f : Mor X Y) (g : Mor Y Z)
           (c : Config X),
      S_map (comp f g) c = S_map g (S_map f c).

  (* Sezioni naturali *)
  Definition Section := forall X : Obj, Config X.

  Definition Natural (eta : Section) : Prop :=
    forall (X Y : Obj) (f : Mor X Y),
      S_map f (eta X) = eta Y.

  (* Struttura locale *)
  Parameter FiniteSub : Obj -> Type.

  Parameter Restrict :
    forall {X : Obj}, Config X -> FiniteSub X -> Type.

  (* Order Property *)
  Definition OP (X : Obj) : Prop :=
    exists (C : nat -> Config X),
      (forall (F : FiniteSub X) (i j : nat),
          Restrict (C i) F = Restrict (C j) F)
      /\
      (forall (i j : nat), i <> j -> C i <> C j).

  (* Assioma D2 *)
  Axiom OP_no_natural_section :
    forall X : Obj,
      OP X ->
      ~(exists eta : Section, Natural eta).

End FORMAL_CORE.

