From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From mathcomp Require Import eqtype choice finfun finmap tuple.
From eventstruct Require Import utils porf_eventstruct inhtype.
From eventstruct Require Import transitionsystem ident.

(******************************************************************************)
(* Here we want to define big-step semaintics of simple register machine in   *)
(* terms of porf_eventstruct                                                  *)
(* This file contains definition of:                                          *)
(*       instr == regmachine instructions                                     *)
(*     seqprog == sequence on instructions ie. one thread of program          *)
(*     parprog == consurent program (contains several threads)                *)
(*  thrd_state == state of one thread: pair of our place in program (ie. line *)
(*            number) and map from registers to values                        *)
(*  init_state == initial state of one thread : pair of 0 default map that    *)
(*     maps all registers to default value                                    *)
(*      config == configuration of program: pair of porf_eventstruct          *)
(*           corresponding to our program in current state and map form       *)
(*           elements of this event structure to corresponding thread states  *)
(*  thrd_sem == if we are in some thread state we can make one step in program*)
(*     and obtain side effect (action on shared locals) and a new thread state*)
(*     But if we want to read from shared memory, in general we can do it in  *)
(*     defferent ways. So as a read-from-shared-memory-side effect we return  *)
(*     Read x __  ie. read with hole instead of read value. And as a mapping  *)
(*     from registers to values we return somehow codded function hole        *)
(*  ltr_thrd_sem == version of thrd_sem as labeled relation                   *)
(*        es_seq == takes event structure `es`, location `x`, predsessor event*)
(*          `pr` and returns sequence of `es + Read x v`, where v runs on all *)
(*           values  `v` that we can read in location `x`                     *)
(*   ces_seq_aux == all dom_consistent exec_eventstructures from es_seq. In   *)
(*           other words if `es_seq` returns all event structures that we can *)
(*           obtain adding new element to our old event structure, then       *)
(*           `ces_seq_aux` is the sequence of only `dom_consistent` event     *)
(*           structures from `es_seq`                                         *)
(*       ces_seq == ces_seq_aux mapped by Consist (doing so we are obtaining  *)
(*           cexec_eventstructures form consistentent exec_eventstructures)   *)
(*      add_hole == takes `es`, label with hole `l` (look thrd_sem),          *)
(*    predsessor event `pr` and return seq `es + l` where l runs on all labels*)
(*     that can be obtained by filling the hole in `l`                        *)
(*     fresh_tid == returns smallest number of thread that wasn't started in  *)
(*         the current configuration                                          *)
(*     eval_step == takes config `c`, event `pr` and retunrs seq of           *)
(*        configurations `c'` that can be reach form `c` making a step        *)
(*        in thread state corresponding to `pr` in `c`                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section RegMachine.

Open Scope fmap_scope.
Open Scope do_notation.
Open Scope exec_eventstruct_scope.

Import Label.Syntax.

Local Notation M := ModelMonad.ListMonad.t.

Context {E : identType} {Val : inhType}.

(*Notation n := (@n val).*)
(*Notation porf_event_struct := (porf_eventstruct E Val).
Notation prime_porf_event_struct := (prime_porf_eventstruct E Val).*)

(*Notation lab := (@lab val).*)
Notation __ := (tt).

(* Registers --- thread local variables *)
Definition Reg := nat.

(* Thread identifiers *)
Definition Tid := nat.


(* Instruction Set *)
Inductive instr :=
| WriteReg of Val & Reg
| ReadLoc  of Reg & Loc
| WriteLoc of Val & Loc
| CJmp     of Reg & Addr
| Fork     of Tid & Addr
| Join     of Tid
| Exit.

Definition prog := seq instr.

Context (pgm : prog).

Definition empty_prog : prog := [::].

Record thrd_state := Thrd_state {
  ip     : nat;
  regmap :> {fsfun Reg -> Val with inh}
}.

Definition eq_thrd_state st st' :=
  (ip st == ip st') && (regmap st == regmap st').

Lemma eqthrd_stateP : Equality.axiom eq_thrd_state.
Proof.
  by move=> [??] [??]; apply: (iffP andP)=> /= [[/eqP + /eqP]|[]] => <-<-.
Qed.

Canonical thrd_state_eqMixin := EqMixin eqthrd_stateP.
Canonical thrd_state_eqType :=
  Eval hnf in EqType thrd_state thrd_state_eqMixin.

Definition state0 : thrd_state := {| ip := 0; regmap := [fsfun with inh] |}.

Import Label.Syntax.

Notation Lab := (@Lab Val Val).

Definition ltr_thrd_sem (l : Lab) st1 st2 : bool :=
  let ip1 := ip     st1 in
  let ip2 := ip     st2 in
  let r1  := regmap st1 in
  let r2  := regmap st1 in
    (ip1 <= size pgm) &&
    match l, nth Exit pgm (ip st1) with
    | Idle          , WriteReg v r  => 
      [&& ip2 == ip1.+1 & r2 == [fsfun r1 with r |-> v]]
    | Read  x a     , ReadLoc  r y  =>
      [&& ip2 == ip1.+1, x == y & r2 == [fsfun r1 with r |-> a]]
    | Write x a     , WriteLoc b y  =>
      [&& ip2 == ip1.+1, x == y, a == b & r2 == r1]
    | Idle          , CJmp r n      =>
      [&& ip2 == if r1 r != inh then n else ip1.+1 & r2 == r1]
    | ThreadEnd _   , Exit          =>
      [&& ip2 == size pgm & r2 == r1]
    | ThreadFork j m, Fork i n      =>
      [&& ip2 == ip1.+1, i == j, n == m & r2 == r1]
    | ThreadStart _ n, _            =>
      [&& ip2 == n & r2 == r1]
    | ThreadJoin j  , Join i        =>
      [&& ip2 == ip1.+1, i == j & r2 == r1]
    | Eps           , _             => st2 == st1
    | Init          , _             => st2 == st1
    | _        , _ => false
    end.

Definition label := (Lab * thrd_state * thrd_state)%type.

Inductive tr_label := Tr st of ltr_thrd_sem st.1.1 st.1.2 st.2.

Arguments Tr {_}.

Coercion label_of (l : tr_label) :=
  let '(Tr st _) := l in st.

Canonical tr_subType := [subType for label_of].

Definition tr_eqMixin := Eval hnf in [eqMixin of tr_label by <:].
Canonical tr_eqType := Eval hnf in EqType tr_label tr_eqMixin.

Lemma label_inj : injective (label_of).
Proof. exact: val_inj. Qed.

Definition lab_po_synch : rel tr_label := 
  fun (l1 l2 : tr_label) => l1.2 == l2.1.2.

Definition lab_rf_synch : rel tr_label := 
  fun (l1 l2 : tr_label) =>
    let: (lb1, st1, _) := val l1 in
    let: (lb2, st2, _) := val l2 in
    (lb1 \>> lb2) &&
    if lb1 is ThreadFork _ _ then
      st1 == st2
    else true.

Lemma ltr_sem_eps : ltr_thrd_sem Eps state0 state0.
Proof. exact/eq_refl. Qed.

Lemma ltr_sem_init : ltr_thrd_sem Init state0 state0.
Proof. exact/eq_refl. Qed.

Definition label_labMixin :=
  @Lab.Mixin
    tr_label
    _
    lab_po_synch
    lab_rf_synch
    (@Tr (Eps, state0, state0) ltr_sem_eps)
    (@Tr (Init, state0, state0) ltr_sem_eps)
    erefl 
    (eq_refl _) 
    erefl 
    (eq_refl _)
    erefl.

Canonical label_labType := Eval hnf in LabType tr_label label_labMixin.

Notation porf_eventstruct := (@porf_eventstruct E label_labType).
Notation prime_porf_eventstruct := (@prime_porf_eventstruct E label_labType).

End RegMachine.

