(** Loventre_TM_Base.v
    Modello astratto di macchina di Turing per il progetto Loventre. *)

From Stdlib Require Import Arith List Bool.
Import ListNotations.

Module Loventre_TM_Base.

  (** === 1. Symbols and states === *)

  Parameter Symbol   : Type.
  Parameter TM_State : Type.

  (* Un simbolo "bianco" esplicito, usato ai bordi del nastro. *)
  Parameter tm_blank : Symbol.

  (* Stato di halting: quando halting st = true, la TM si considera ferma. *)
  Parameter halting : TM_State -> bool.

  (** === 2. Tape and configurations === *)

  Record Tape := {
    left  : list Symbol;
    head  : Symbol;
    right : list Symbol
  }.

  (* Manteniamo MultiTape per possibili estensioni, anche se non lo usiamo ora. *)
  Definition MultiTape := list Tape.

  Record Config := {
    state : TM_State;
    tape  : Tape
  }.

  (** === 3. Single-step transition === *)

  Inductive MoveDir :=
  | MLeft
  | MRight
  | MStay.

  (* Transizione astratta: dato uno stato e il simbolo sotto la testina,
     restituisce nuovo stato, simbolo da scrivere e direzione del movimento. *)
  Parameter Transition :
    TM_State -> Symbol -> TM_State * Symbol * MoveDir.

  (* Movimento a sinistra della testina. *)
  Definition move_left (tp : Tape) : Tape :=
    match left tp with
    | [] =>
        (* Nessun simbolo a sinistra: comparsa di un bianco. *)
        {| left  := [];
           head  := tm_blank;
           right := head tp :: right tp |}
    | s :: ls =>
        {| left  := ls;
           head  := s;
           right := head tp :: right tp |}
    end.

  (* Movimento a destra della testina. *)
  Definition move_right (tp : Tape) : Tape :=
    match right tp with
    | [] =>
        (* Nessun simbolo a destra: comparsa di un bianco. *)
        {| left  := head tp :: left tp;
           head  := tm_blank;
           right := [] |}
    | s :: rs =>
        {| left  := head tp :: left tp;
           head  := s;
           right := rs |}
    end.

  (* Applica la direzione di movimento. *)
  Definition apply_move (d : MoveDir) (tp : Tape) : Tape :=
    match d with
    | MLeft  => move_left tp
    | MRight => move_right tp
    | MStay  => tp
    end.

  (* Un singolo passo della macchina. *)
  Definition step (c : Config) : Config :=
    let st := state c in
    let tp := tape c in
    let '(st', sym', dir) := Transition st (head tp) in
    let tp_written :=
      {| left  := left tp;
         head  := sym';
         right := right tp |} in
    let tp' := apply_move dir tp_written in
    {| state := st'; tape := tp' |}.

  (** Alias concettuale: evoluzione di un passo. *)
  Definition next (c : Config) : Config := step c.

  (** === 4. Execution with fuel === *)

  Fixpoint run_fuel (n : nat) (c : Config) : Config :=
    match n with
    | O => c
    | S n' =>
        if halting (state c) then c
        else run_fuel n' (step c)
    end.

  (** Alias: iterated TM step. *)
  Definition TM_step (n : nat) (c : Config) : Config :=
    run_fuel n c.

  (** === 5. Overflow and stability predicates === *)

  (* Overflow: nastro “troppo grande” — soglia simbolica, da collegare alla
     parte geometrica. *)
  Definition overflow (c : Config) : Prop :=
    length (left (tape c)) + length (right (tape c)) > 1000000.

  (* Configurazione stabile: stato di halting. *)
  Definition stable_conf (c : Config) : Prop :=
    halting (state c) = true.

  (** === 6. Local configuration complexity === *)

  Definition complexity_conf (c : Config) : nat :=
    length (left (tape c)) + length (right (tape c)).

  (* Modello base: tempo = fuel; le TM concrete potranno specializzare. *)
  Definition time_function (n : nat) : nat := n.

  (** === 7. Acceptance and words === *)

  Definition Word := list bool.

  (* Come un input booleano viene codificato sul nastro. *)
  Parameter input_of_word : Word -> Tape.

  (* La TM (descritta da una configurazione iniziale `tm`) accetta w entro t
     se, partendo da tm con il nastro impostato su w, entra in stato di halting
     entro t passi. *)
  Definition accepts_in (tm : Config) (w : Word) (t : nat) : bool :=
    let c0 :=
      {| state := state tm;
         tape  := input_of_word w |} in
    halting (state (run_fuel t c0)).

  (** === 8. Polytime configuration (placeholder) === *)

  (* Versione astratta: esiste un polinomio p di grado <= 3 che limita
     il tempo di accettazione su tutte le parole. In futuro andrà collegato
     a Loventre_Complexity.inP. *)
  Definition polytime_config (c : Config) : Prop :=
    exists p : nat -> nat,
      (forall n, p n <= n ^ 3) /\
      forall w : Word,
        accepts_in c w (p (length w)) = true.

End Loventre_TM_Base.

