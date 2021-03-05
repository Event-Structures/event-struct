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
  evstr    : cexec_event_struct;
  trhdmap  :> {fsfun E -> (thrd_state * option nat)%type with (init_state, None)}
}.

Variable prog : parprog.

Notation inth := (nth (CJmp 0 0)).
Notation nth_tid := (nth [::]).

Definition thrd_sem (pgm : seqprog) (st : thrd_state) :
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

Definition ltr_thrd_sem (l : option (@label V V)) pgm st1 st2 : bool :=
  match thrd_sem pgm st1, l with
  | (Some (Write x v), st), Some (Write y u) => [&& x == y, v == u & st inh == st2]
  | (Some (Read  x _), st), Some (Read  y u) => (x == y) && (st u == st2)
  | (None            , st), None             => st inh == st2
  | _, _                                     => false
  end.

Variable (es : cexec_event_struct).
Notation domain      := (dom es).
Notation lab      := (lab es).
Notation ffpred   := (fpred es).
Notation ffrf     := (frf es).
Notation fresh_id := (fresh_seq domain).

Arguments add_label_of_Nread {_ _ _ _} _ {_}.

Definition wval (l : @label V V) : V :=
  if l is Write _ v then v else inh.

Definition wpred (x : loc) (w : E) :=
   (lloc (lab w) == Some x) && (is_write (lab w)).

Arguments wpred /.

Definition writes_seq x := [seq y <- domain | wpred x y].

Lemma ws_mem x w : w \in writes_seq x -> w \in fresh_id :: domain .
Proof. by rewrite ?inE mem_filter => /andP[?->]. Qed.

Lemma ws_wpred x w :
  w \in writes_seq x ->
  add_wr w fresh_id lab (Read x (wval (lab w))).
Proof.
  rewrite mem_filter=> /andP[] /=.
  case: (lab w)=> //= [?? /andP[]|?? /andP[/eqP[->]]] //; by rewrite ?eq_refl.
Qed.

(* TODO: filter by consistentcy *)
Definition es_seq x {pr} : (seq (exec_event_struct * E)) :=
  if pr \in fresh_id :: domain =P true is ReflectT pr_mem then
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
        wr
      ) | w <- (seq_in (writes_seq x))]
  else [::].


Definition ces_seq_aux x pr := 
  [seq estr_w <- @es_seq x pr | 
    let: (estr, w) := estr_w in
   ~~ (cf estr fresh_id w)].

Lemma mem_ces_seq_aux x pr ces: 
  ces \in (@ces_seq_aux x pr) -> dom_consistency ces.1.
Proof.
  case: ces => ces w; rewrite mem_filter /= /es_seq => /andP[?].
  case: eqP=> // ? /mapP[?? [/[dup] C -> ws]].
  apply/consist_add_event=> /=; first by case: es.
  by rewrite -C -ws.
Qed.

Definition ces_seq x {pr} := 
  [seq 
    let: ces_w    := sval ces_w_mem in
    let: (ces, w) := ces_w in
    let: ces_mem  := valP ces_w_mem in 
    (Consist (mem_ces_seq_aux ces_mem), wval (lab w)) | 
    ces_w_mem <- seq_in (@ces_seq_aux x pr)].

Arguments consist_Nread {_ _ _}.

Definition add_hole
  (l : @label unit V) pr :
  seq (cexec_event_struct * V) :=
  if pr \in fresh_id :: domain =P true is ReflectT pr_mem then
    match l with
    | Write x v => 
      [:: (Consist (consist_Nread es pr (Write x v) erefl pr_mem), v)]  
    | Read x __ => @ces_seq x pr
    | _         => [::]
    end
  else [::].

Definition eval_step (c : config) {pr : E}
  : seq config :=
  let: Config es tmap := c in
  let: (conf, otid)    := tmap pr in
    flatten [seq
      let: (l, cont_st) := thrd_sem (nth_tid prog t) conf in
        if l is Some l then
          [seq let: (e, v) := x in
                (Config e [fsfun c with fresh_id |-> (cont_st v, Some t)]) |
                x <- add_hole l pr]
        else
          [:: Config es [fsfun c with pr |-> (cont_st inh, Some t)]] 
      | t <- 
        if otid is Some tid then
          [:: tid]
        else iota 0 (size prog)
    ].

End RegMachine.
