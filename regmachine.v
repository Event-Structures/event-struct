From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order.
From mathcomp Require Import eqtype fingraph path finmap choice finfun. 
From event_struct Require Import utilities eventstructure inhtype.
From event_struct Require Import transitionsystem ident rfsfun.

(******************************************************************************)
(* Here we want to obrain big-step semaintics of simple register machine in   *)
(* terms of fin_exec_event_structures                                         *)
(* This file contains definition of:                                          *)
(*             instr == regmachine instructions                               *)
(*             seqprog == sequence on instructions ie. one thread of program  *)
(*             parprog == consurent program (contains several threads)        *)
(*             thrd_state == state of one thread: pair of our place in        *)
(*               program (ie. line numder) and map from registers to values   *)
(*             init_state == initial state of one thred : pair of 0 default   *)
(*               map that maps all registers to default value                 *)
(*             config == configuration of program: pair of                    *)
(*               fin_exec_event_strucure corresponding to our program in      *)
(*               current state and map form elements of this event structure  *)
(*               to corresponding thread states                               *)
(*             thrd_sem == if we are in some thread state we can make one     *)
(*               step in program and obtain side effect (action on shared     *)
(*               locals) and a new thread state. But if we want to read from  *)
(*               shared memory, in general we can do it in defferent ways. So *)
(*               as a read-from-shared-memory-side effect we return Read x __ *)
(*               ie. read with hole instead of read value. And as a mapping   *) 
(*               from registers to values we return somehow codded function   *)
(*               hole                                                         *)
(*             ltr_thrd_sem == version of thrd_sem as labeled relation        *)
(*             writes_seq == function that takes local variable x and         *)
(*               some event structure and returns all events in this event    *)
(*               structure that are writing in x                              *)
(*             es_seq == takes event structure `es`, location `x`, predsessor *)
(*               event `pr` and returns sequence of `es + Read x v`, where v  *)
(*               runs on all values  `v` that we can read in location `x`     *)
(*             add_hole == takes `es`, label with hole `l` (look thrd_sem),   *)
(*               predsessor event `pr` and return seq `es + l` where l runs   *)
(*               on all labels that can be obtained by filling the hole in `l`*)
(*             eval_step == takes config `c`, event `pr` and retunrs seq of   *)
(*               configurations `c'` that can be reach form `c` making a step *)
(*               in thread state corresponding to `pr` in `c`                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Arguments Read {_ _}.
Arguments Write {_ _}.

Section RegMachine.

Open Scope fmap.
Context {val : inhType} {disp} {E : identType disp}.

(*Notation n := (@n val).*)
Notation exec_event_struct := (@fin_exec_event_struct val _ E).

(*Notation lab := (@lab val).*)
Notation __ := (tt).

(* Registers --- thread local variables *)
Definition reg := nat. 

(* Instruction *)
Inductive instr :=
| WriteReg : val -> reg -> instr
| ReadLoc  : reg -> loc -> instr
| WriteLoc : val -> loc -> instr
| CJmp     : reg -> nat -> instr.

Definition seqprog := seq instr.

Definition parprog := seq seqprog.

Definition thrd_state := (nat * {fsfun reg -> val with inh})%type.

Definition init_state : thrd_state := (0, [fsfun with inh]).

Record config := Conf {
  evstr : exec_event_struct;
  corr  :> {fsfun E -> thrd_state with init_state}
}.

Variable p : seqprog.

Notation nth := (nth (CJmp 0 0)).

Definition thrd_sem (st : thrd_state) :
  (option (@label unit val) * (val -> thrd_state))%type :=
  let: (ip, map) := st in
  match nth p ip with
  | WriteReg v r => (none,             fun _ => 
                                       (ip.+1, [fsfun map with r |-> v]))
  | ReadLoc  r x => (some (Read x __), fun v => 
                                       (ip.+1, [fsfun map with r |-> v]))
  | WriteLoc v x => (some (Write x v), fun _ => (ip.+1, map))
  | CJmp     r n => (none,             fun _ => 
                                       (if map r != inh then n else ip.+1, map))
  end.

Definition ltr_thrd_sem (l : option (@label val val)) (st1 st2 : thrd_state) : bool :=
  match thrd_sem st1, l with
  | (some (Write x v), st), some (Write y u) => [&& x == y, v == u & st inh == st2]
  | (some (Read  x _), st), some (Read  y u) => (x == y) && (st u == st2)
  | (none            , st), none             => st inh == st2
  | _, _                                     => false
  end.

Variable (es : exec_event_struct).
Notation dom := (dom es).
Notation lab    := (lab es).
Notation ffpred  := (ffpred es).
Notation ffrf    := (ffrf es).
Notation fresh := (fresh_seq dom).

Arguments add_label_of_Nread {_ _ _ _} _ {_}.

Definition wval (l : @label val val) : val := 
  if l is Write _ v then v else inh.

Definition wpred (x : loc) (w : E)
  := (lab w) << (Read x (wval (lab w))).

Arguments wpred /.

Definition writes_seq x :
  seq (sig_subType (fun y => (wpred x y) && (y \in dom))) :=
  pmap insub dom.

Lemma ws_mem x 
   (w : sig_subType (fun y => (wpred x y) && (y \in dom))):
   (eqtype.val w) \in fresh :: dom .
Proof.
  rewrite ?inE.
  by case: w=> /= ? /andP[?->]. 
Qed.

Lemma ws_wpred x 
  (w : sig_subType (fun y => (wpred x y) && (y \in dom))):
  let: wr := eqtype.val w in
  let: read_lab := Read x (wval (lab wr)) in
    ((wr == fresh) && ~~ is_read read_lab) ||
    (lab wr) << read_lab.
Proof. by case: w=> /= ? /andP[->]. Qed.

(* TODO: filter by consistentcy *)
Definition es_seq x {pr} (pr_mem : pr \in fresh :: dom) :
 (seq (exec_event_struct * val)) := 
  map (fun w => 
   ((add_event 
    (
      Add pr_mem (@ws_mem x w) (ws_wpred w))),
      wval (lab (eqtype.val w)))
    )
     (writes_seq x).

Definition add_hole  
  (l : @label unit val) {pr} (pr_mem : pr \in fresh :: dom) :
  seq (exec_event_struct * val) :=
  match l with
  | Write x v => 
    [:: (add_event (add_label_of_Nread (Write x v) pr_mem erefl), v)]
  | Read x __ => es_seq x pr_mem
  | _ => [::]
  end.

Definition eval_step (c : config) {pr} (pr_mem : pr \in fresh :: dom) 
  : seq config :=
  let: (l, cont_st) := thrd_sem (c pr) in
  if l is some l then
    [seq (Conf x.1 [fsfun c with fresh |-> cont_st x.2]) |
     x <- (add_hole l pr_mem)]
  else [:: Conf (evstr c) [fsfun c with pr |-> cont_st inh]].

End RegMachine.
