From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From mathcomp Require Import eqtype choice finfun finmap.
From event_struct Require Import utilities eventstructure inhtype.
From event_struct Require Import transitionsystem ident.

(******************************************************************************)
(* Here we want to define big-step semaintics of simple register machine in   *)
(* terms of fin_exec_event_structures                                         *)
(* This file contains definition of:                                          *)
(*       instr == regmachine instructions                                     *)
(*     seqprog == sequence on instructions ie. one thread of program          *)
(*     parprog == consurent program (contains several threads)                *)
(*  thrd_state == state of one thread: pair of our place in program (ie. line *)
(*            number) and map from registers to values                        *)
(*  init_state == initial state of one thread : pair of 0 default map that    *)
(*     maps all registers to default value                                    *)
(*      config == configuration of program: pair of fin_exec_event_structure  *)
(*           corresponding to our program in current state and map form       *)
(*           elements of this event structure to corresponding thread states  *)
(*  thrd_sem == if we are in some thread state we can make one step in program*)
(*     and obtain side effect (action on shared locals) and a new thread state*)
(*     But if we want to read from shared memory, in general we can do it in  *)
(*     defferent ways. So as a read-from-shared-memory-side effect we return  *)
(*     Read x __  ie. read with hole instead of read value. And as a mapping  *)
(*     from registers to values we return somehow codded function hole        *)
(*  ltr_thrd_sem == version of thrd_sem as labeled relation                   *)
(*    writes_seq == function that takes local variable x and some event       *)
(*          structure and returns all events in this event structure that are *)
(*          writing in x                                                      *)
(*        es_seq == takes event structure `es`, location `x`, predsessor event*)
(*          `pr` and returns sequence of `es + Read x v`, where v runs on all *)
(*           values  `v` that we can read in location `x`                     *)
(*      add_hole == takes `es`, label with hole `l` (look thrd_sem),          *)
(*    predsessor event `pr` and return seq `es + l` where l runs on all labels*)
(*     that can be obtained by filling the hole in `l`                        *)
(*     eval_step == takes config `c`, event `pr` and retunrs seq of           *)
(*        configurations `c'` that can be reach form `c` making a step        *)
(*        in thread state corresponding to `pr` in `c`                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section RegMachine.

Open Scope fmap.
Context {V : inhType} {disp} {E : identType disp}.

(*Notation n := (@n val).*)
Notation exec_event_struct := (@fin_exec_event_struct V _ E).
Notation cexec_event_struct := (@cexec_event_struct V _ E).

<<<<<<< HEAD
=======
Definition eq_es (es es' : exec_event_struct) : bool :=
  [&& dom es == dom es' & lprf es == lprf es'].

Lemma eqesP : Equality.axiom eq_es.
Proof.
move=> x y; apply: (iffP idP)=> [|->]; last by rewrite /eq_es ?eq_refl.
case: x=> d1 ds1 l1 s1 lab1; rewrite {}/lab1 => pc1 rc1.
case: y=> d2 ds2 l2 s2 lab2; rewrite {}/lab2 => pc2 rc2.
case/andP=> /= /eqP E1 /eqP E2.
move: E1 E2 ds1 s1 pc1 rc1 ds2 s2 pc2 rc2; (do 2 case: _ /).
move=> ds1 s1 pc1 rc1 ds2 s2 pc2 rc2.
suff Eqs: (((ds1 = ds2) * (s1 = s2)) * ((pc1 = pc2) * (rc1 = rc2)))%type.
- by rewrite ?Eqs.
do ? split; exact: eq_irrelevance.
Qed.

Canonical es_eqMixin := EqMixin eqesP.
Canonical es_eqType := Eval hnf in EqType exec_event_struct es_eqMixin.


>>>>>>> 4410f272ba3bc98c533f019a3183a783c3245c47
(*Notation lab := (@lab val).*)
Notation __ := (tt).

(* Registers --- thread local variables *)
Definition reg := nat.

(* Instruction Set *)
Inductive instr :=
| WriteReg : V -> reg -> instr
| ReadLoc  : reg -> loc -> instr
| WriteLoc : V -> loc -> instr
| CJmp     : reg -> nat -> instr.

Definition seqprog := seq instr.

Definition parprog := seq seqprog.

Record thrd_state := Thrd_state {
  ip     : nat;
  regmap : {fsfun reg -> V with inh}
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

Definition init_state : thrd_state := {| ip := 0; regmap := [fsfun with inh] |}.

Record config := Config {
  evstr    : exec_event_struct;
  trhdmap  :> {fsfun E -> thrd_state with init_state}
}.

Variable pgm : seqprog.

Notation inth := (nth (CJmp 0 0)).

Definition thrd_sem (st : thrd_state) :
  (option (@label unit V) * (V -> thrd_state))%type :=
  let: {| ip := ip; regmap := rmap |} := st in
  match inth pgm ip with
  | WriteReg v r => (None,
                     fun _ => {| ip     := ip.+1;
                                 regmap := [fsfun rmap with r |-> v] |})
  | ReadLoc  r x => (Some (Read x __),
                     fun v => {| ip     := ip.+1;
                                 regmap := [fsfun rmap with r |-> v] |})
  | WriteLoc v x => (Some (Write x v),
                     fun _ => {| ip     := ip.+1;
                                 regmap := rmap |})
  | CJmp     r n => (None,
                     fun _ => {| ip     := if rmap r != inh then n else ip.+1;
                                 regmap := rmap |} )
  end.

Definition ltr_thrd_sem (l : option (@label V V)) st1 st2 : bool :=
  match thrd_sem st1, l with
  | (Some (Write x v), st), Some (Write y u) => [&& x == y, v == u & st inh == st2]
  | (Some (Read  x _), st), Some (Read  y u) => (x == y) && (st u == st2)
  | (None            , st), None             => st inh == st2
  | _, _                                     => false
  end.

Variable (es : exec_event_struct).
Notation dom      := (dom es).
Notation lab      := (lab es).
Notation ffpred   := (fpred es).
Notation ffrf     := (frf es).
Notation fresh_id := (fresh_seq dom).

Arguments add_label_of_Nread {_ _ _ _} _ {_}.

Definition wval (l : @label V V) : V :=
  if l is Write _ v then v else inh.

Definition wpred (x : loc) (w : E) :=
   (lloc (lab w) == Some x) && (is_write (lab w)).

Arguments wpred /.

Definition writes_seq x := [seq y <- dom | wpred x y].

Lemma ws_mem x w : w \in writes_seq x -> w \in fresh_id :: dom .
Proof. by rewrite ?inE mem_filter => /andP[?->]. Qed.

Lemma ws_wpred x w :
  w \in writes_seq x ->
  add_wr w fresh_id lab (Read x (wval (lab w))).
Proof.
  rewrite mem_filter=> /andP[] /=.
  case: (lab w)=> //= [?? /andP[]|?? /andP[/eqP[->]]] //; by rewrite ?eq_refl.
Qed.

(* TODO: filter by consistentcy *)
Definition es_seq x {pr} (pr_mem : pr \in fresh_id :: dom) : (* -- proof *)
 (seq (exec_event_struct * V)) :=
  [seq
    let: wr       := sval w in
    let: w_in     := valP w in
    let: read_lab := Read x (wval (lab wr)) in
    (
      add_event
        {| add_lb            := read_lab;
           add_pred_in_dom   := pr_mem;
           add_write_in_dom  := ws_mem   w_in;
           add_write_consist := ws_wpred w_in; |},
      wval (lab (eqtype.val w))
    ) | w <- (seq_in (writes_seq x))].

Definition add_hole
  (l : @label unit V) {pr} (pr_mem : pr \in fresh_id :: dom) :
  seq (exec_event_struct * V) :=
  match l with
  | Write x v =>
    [:: (add_event (add_label_of_Nread (Write x v) pr_mem erefl), v)]
  | Read x __ => es_seq x pr_mem
  | _ => [::]
  end.

Definition eval_step (c : config) {pr} (pr_mem : pr \in fresh_id :: dom)
  : seq config :=
  let: (l, cont_st) := thrd_sem (c pr) in
  if l is Some l then
    [seq let: (e, v) := x in
          (Config e [fsfun c with fresh_id |-> cont_st v]) |
          x <- (add_hole l pr_mem)]
  else
    [:: Config (evstr c) [fsfun c with pr |-> cont_st inh]].

End RegMachine.
