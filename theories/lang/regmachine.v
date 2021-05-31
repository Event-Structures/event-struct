From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From mathcomp Require Import eqtype choice finfun finmap tuple.
From monae Require Import hierarchy monad_model.
From eventstruct Require Import utils eventstructure inhtype.
From eventstruct Require Import transitionsystem ident.

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

Context {disp} {E : identType disp} {Val : inhType}.

(*Notation n := (@n val).*)
Notation exec_event_struct := (fin_exec_event_struct E Val).
Notation cexec_event_struct := (cexec_event_struct E Val).

(*Notation lab := (@lab val).*)
Notation __ := (tt).

(* Registers --- thread local variables *)
Definition Reg := nat.

(* Instruction Set *)
Inductive instr :=
| WriteReg of Val & Reg 
| ReadLoc  of Reg & Loc
| WriteLoc of Val & Loc 
| CJmp     of Reg & nat 
| Stop.

Definition seqprog := seq instr.

Definition empty_prog : seqprog := [::].

Definition parprog := seq seqprog.

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

Definition init_state : thrd_state := {| ip := 0; regmap := [fsfun with inh] |}.

Record config := Config {
  evstr    : cexec_event_struct;
  trhdmap  :> {fsfun E -> (thrd_state * nat)%type with (init_state, 0)}
}.

Notation inth := (nth Stop).

Definition thrd_sem (pgm : seqprog) (st : thrd_state) :
  (option (@Lab unit Val) * (Val -> thrd_state))%type :=
  let: {| ip := ip; regmap := rmap |} := st in
  if ip == 0 then
    (Some ThreadStart, fun=> {| ip := 1; regmap := rmap |})
  else
    match inth pgm ip.-1 with
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
                      fun _ => {| ip     := if rmap r != inh then n.+1 else ip.+1;
                                  regmap := rmap |} )
    | Stop         => (None, fun=> st)
    end.

Definition ltr_thrd_sem (l : option (@Lab Val Val)) pgm st1 st2 : bool :=
  match thrd_sem pgm st1, l with
  | (Some (Write x v), st), Some (Write y u) => [&& x == y, v == u & st inh == st2]
  | (Some (Read  x _), st), Some (Read  y u) => (x == y) && (st u == st2)
  | (Some ThreadStart, st), Some ThreadStart => st inh == st2
  | (None            , st), None             => st inh == st2
  | _, _                                     => false
  end.

Variable (es : cexec_event_struct).
Notation ffpo     := (fpo es).
Notation ffrf     := (frf es).
Notation fresh_id := (fresh_seq (dom es)).

(* Arguments add_label_of_Nread {_ _ _ _} _ {_}. *)

Lemma ws_mem x w : 
  w \in [events of es | is_write & with_loc x] -> w \in dom es.
Proof. by rewrite ?inE mem_filter => /andP[?->]. Qed.

Lemma ws_wpred x w :
  w \in [events of es | is_write & with_loc x] ->
  (lab es w) \>> (Read x (odflt inh (value es w))).
Proof.
  rewrite mem_filter=> /andP[] /=.
  rewrite /is_write /with_loc /loc /value.
  rewrite /Label.synch /Label.is_write /Label.value /Label.loc /=. 
  case: (lab es w)=> l v //=. 
  move=> /[swap] ? /eqP ->. 
  by rewrite !eq_refl.
Qed.

Definition es_seq x {pr} : (seq (exec_event_struct * E)) :=
  if pr \in dom es =P true is ReflectT pr_mem then
    [seq
      let: wr       := sval w in
      let: w_in     := valP w in
      let: read_lab := Read x (odflt inh (value es wr)) in
      (
        add_new_event
          {| add_lb            := read_lab;
             add_pred_in_dom   := pr_mem;
             add_write_in_dom  := ws_mem   w_in;
             add_write_consist := ws_wpred w_in; |},
        wr
      ) | w <- seq_in [events of es | is_write & with_loc x]]
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
  move: C. rewrite /add_new_event; case: ifP=> _ C; first by case: es.
  apply/consist_add_event=> /=; first by case: es.
  by rewrite -C -ws.
Qed.

Definition ces_seq x pr := 
  [seq 
    let: ces_w    := sval ces_w_mem in
    let: (ces, w) := ces_w in
    let: ces_mem  := valP ces_w_mem in 
    (Consist _ (mem_ces_seq_aux ces_mem), odflt inh (value es w)) | 
    ces_w_mem <- seq_in (@ces_seq_aux x pr)].

Arguments consist_new_nread {_ _ _}.

Definition add_hole
  (l : @Lab unit Val) pr :
  seq (cexec_event_struct * Val) :=
  if pr \in dom es =P true is ReflectT pr_mem then
    match l with
    | Write x v => 
      [:: (Consist _ (consist_new_nread es pr (Write x v) pr_mem erefl), v)]  
    | ThreadStart =>
      [:: (Consist _ (consist_new_nread es pr ThreadStart pr_mem erefl), inh)]
    | Read x __ => ces_seq x pr
    | _         => [::]
    end
  else [::].

Variable prog : parprog.

Definition fresh_tid (c : config) := 
  foldr maxn 0 [seq (snd x).+1 | x <- fgraph (fmap_of_fsfun c)].

Definition eval_step (c : config) pr : seq config := 
  let: Config es tmap := c in
  let: (conf, tid)    := tmap pr in
  let: tid            := if pr \in dom es then tid else fresh_tid c in
  let: (l, cont_st)   := thrd_sem (nth empty_prog prog tid) conf in
    if l is Some l then do 
      ev <- add_hole l pr : M _;
      let '(e, v) := ev in
        [:: Config e  [fsfun c with fresh_id |-> (cont_st v, tid)]]
    else
      [:: Config es [fsfun c with pr |-> (cont_st inh, tid)]].

End RegMachine.
