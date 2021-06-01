From RelationAlgebra Require Import lattice monoid rel kat kat_tac kleene.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From mathcomp Require Import eqtype choice finfun finmap tuple order.
From monae Require Import hierarchy monad_model.
From eventstruct Require Import utils eventstructure inhtype.
From eventstruct Require Import transitionsystem ident rewriting_system.

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

Definition eq_instr st st' :=
  match st, st' with
  | WriteReg x r, WriteReg y s => [&& x == y & r == s]
  | ReadLoc  x l, ReadLoc  y m => [&& x == y & l == m]
  | WriteLoc x l, WriteLoc y m => [&& x == y & l == m]
  | CJmp     r n, CJmp     s m => [&& r == s & n == m]
  | Stop        , Stop         => true
  | _           , _            => false
  end.

Lemma eqinstrP : Equality.axiom eq_instr.
Proof.
  case=> [??|??|??|??|][]*/=; (try by constructor); 
  by apply/(iffP andP)=> [[/eqP->/eqP]->|[->->]].
Qed.

Canonical instr_eqMixin := EqMixin eqinstrP.
Canonical instr_eqType  := Eval hnf in EqType instr instr_eqMixin.

Definition prog := seq instr.

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

Definition init_state : thrd_state := {| ip := 0; regmap := [fsfun with inh] |}.

Record config := Config {
  evstr     :> exec_event_struct;
  thrdmap   : {fsfun E -> thrd_state with init_state}
}.

Definition eq_config c c' :=
  (evstr c == evstr c') && (thrdmap c == thrdmap c').

Lemma eqconfigP : Equality.axiom eq_config.
Proof.
  by move=> [??] [??]; apply: (iffP andP)=> /= [[/eqP + /eqP]|[]] => <-<-.
Qed.

Canonical config_eqMixin := EqMixin eqconfigP.
Canonical config_eqType  := Eval hnf in EqType config config_eqMixin.

Coercion thrdmap : config >-> fsfun.

Definition thrd_prositions := 
  let fix thrd_pos s n pgm :=
    match pgm with
    | [::]        => s
    | ins :: pgm => 
      if ins == Stop then
        thrd_pos (n :: s) n.+1 pgm
      else thrd_pos s n pgm
    end in
      thrd_pos [::] 1%N.

Definition prog_sem (pgm : prog) (st : thrd_state) :
  seq (@Lab unit Val * (Val -> thrd_state)) :=
  let: {| ip := ip; regmap := rmap |} := st in
  if ip == 0%N then do 
    ip <- thrd_prositions pgm : M _;
                      [:: (ThreadStart,
                      fun _ => {| ip     := ip.+1;
                                  regmap := rmap |})]
  else
    match nth Stop pgm ip.-1 with
    | WriteReg v r => [:: (Eps,
                      fun _ => {| ip     := ip.+1;
                                  regmap := [fsfun rmap with r |-> v] |})]
    | ReadLoc  r x => [:: (Read x __,
                      fun v => {| ip     := ip.+1;
                                  regmap := [fsfun rmap with r |-> v] |})]
    | WriteLoc v x => [:: (Write x v,
                      fun _ => {| ip     := ip.+1;
                                  regmap := rmap |})]
    | CJmp     r n => [:: (Eps,
                      fun _ => {| ip     := if rmap r != inh then n.+1 else ip.+1;
                                  regmap := rmap |} )]
    | Stop         => [:: (Eps, fun=> st)]
    end.

Section AddHole.

Variable (es : exec_event_struct).
Notation ffpred   := (fpo es).
Notation ffrf     := (frf es).
Notation fresh_id := (fresh_seq (dom es)).

Arguments add_label_nread {_ _ _ _ _} _.

Lemma ws_mem x w :
  w \in [events of es | is_write & with_loc x] -> w \in dom es.
Proof. by rewrite ?inE mem_filter => /andP[?->]. Qed.

Import Label.Syntax. 

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

Definition es_seq x pr : (seq (exec_event_struct * Val)) :=
  if pr \in dom es =P true is ReflectT pr_mem then
    [seq
      let: wr       := sval w in
      let: w_in     := valP w in
      let: read_lab := Read x (odflt inh (value es wr)) in
      (
        add_event
          {| add_lb            := read_lab;
             add_lb_init       := erefl;
             add_pred_in_dom   := pr_mem;
             add_write_in_dom  := ws_mem   w_in;
             add_write_consist := ws_wpred w_in; |},
          (odflt inh (value es wr))
      ) | w <- seq_in [events of es | is_write & with_loc x]]
  else [::].

Definition add_hole (l : @Lab unit Val) pr : 
  seq (exec_event_struct * Val) :=
  if pr \in dom es =P true is ReflectT pr_mem then
    match l with
    | Read  x _   => es_seq x pr
    | Write x v   =>
      [:: (add_event (add_label_nread (Write x v) pr_mem erefl erefl), v)]
    | ThreadStart =>
      [:: (add_event (add_label_nread ThreadStart pr_mem erefl erefl), inh)]
    | ThreadEnd   =>
      [:: (add_event (add_label_nread ThreadEnd pr_mem erefl erefl), inh)]
    | _           => [::]
    end
  else [::].

End AddHole.

Variable pgm : prog.

Definition eval_step (c : config) pr : seq config := 
  if pr \in dom c then 
    do prg_st <- prog_sem pgm (c pr) : M _;
    let: (l, cont_st) := prg_st in
      if l != Eps then do 
        ev <- add_hole c l pr : M _;
        let '(e, v) := ev in
          [:: Config e [fsfun c with fresh_seq (dom c) |-> cont_st v]]
      else
        [:: Config c [fsfun c with pr |-> cont_st inh]]
  else [::].

End RegMachine.

Notation fresh_id1  es := (fresh_seq (dom es)).
Notation fresh_id2 es := (fresh_seq (fresh_seq (dom es) :: dom es)).

Module AddHole.

Section AddHoleConfl.

Open Scope fmap_scope.
Open Scope do_notation.
Open Scope exec_eventstruct_scope.

Context {disp} {E : identType disp} {Val : inhType}.

(*Notation n := (@n val).*)
Notation exec_event_struct := (fin_exec_event_struct E Val).
Notation cexec_event_struct := (cexec_event_struct E Val).

Definition ltr (l : (@Lab unit Val) * E * Val) es es'
  := (es', l.2) \in add_hole es l.1.1 l.1.2.

Definition tr es es' := exists (l : (@Lab unit Val)) (pr : E) (v : Val),
   (es', v) \in add_hole es l pr.

Notation "e1 '~(' l ',' pr ',' v ')~>' e2" := (ltr (l, pr, v) e1 e2) (at level 20).

Lemma exlab_tr : tr ≡ exlab ltr.
Proof.
  move=> ??; split=> [[l [pr [v]]]|[[[l pr v]]]] ?; 
  by [exists (l, pr, v)| exists l, pr, v].
Qed.

Notation "e1 '~>' e2" := (tr e1 e2).

Definition fill_hole (l : @Lab unit Val) (v : Val) := 
  match l with
  | Read x _    => Read x v
  | Write x v   => Write x v
  | ThreadStart => ThreadStart
  | ThreadEnd   => ThreadEnd
  | Eps         => Eps
  | Init        => Init
  end.

Definition mk_hole (l : @Lab Val Val) := 
  match l with
  | Read x v    => Read x tt
  | Write x v   => Write x v
  | ThreadStart => ThreadStart
  | ThreadEnd   => ThreadEnd
  | Eps         => Eps
  | Init        => Init
  end.

Lemma fill_mk_hole l : fill_hole (mk_hole l) (odflt inh (Label.value l)) = l.
Proof. by case: l. Qed.

Import Label.Syntax.

Arguments add_nread_synch {_ _ _ _} _.

Lemma ltrP {es1 es2 la pr v} :
  reflect
  (exists (l : edescr E Lab),
  [/\ AddEvent.ltr l es1 es2,
      fpo_prj l                           = pr,
      fill_hole la v                      = lab_prj l &
      odflt inh (Label.value (lab_prj l)) = v])
  (es1 ~(la, pr, v)~> es2).
Proof.
  apply: (iffP idP).
  - rewrite /ltr /= /add_hole; case: eqP=> // p.
    case: la=> //=.
    - move=> l ?; rewrite /es_seq; case: eqP=> // ?.
      rewrite seq_inE=> /mapP=> [[[/= e p' I [-> El]]]].
      exists (mk_edescr (Read l v) pr e); split=> //.
      apply/AddEvent.ltr_add=> /=; by rewrite El.
    1-3: move=>>; rewrite ?inE=> /eqP [-><-];
      eexists (mk_edescr _ pr \i0); split=> //;
      exact/AddEvent.ltr_add.
  rewrite /ltr /==> [[[/= l p w [+ <-]]]].
  move=> /[dup][[[/= ??? + ??? _ []]]]; move=> /[swap]{1 2}<- ni ??.
  move=> /[dup] /AddEvent.ltr_po /= Ip /[swap]++/[swap].
  rewrite /add_hole; case: eqP=> [?|]; last by rewrite Ip.
  case: la=> /=.
  - move=> la _ <- /= _ [[l' p' w' +++++ [el ep ew]]].
    case: _ / ep el ew; (do ? case: _ /)=> ?? wd wc ->.
    rewrite /es_seq; case: eqP=> [?|]; last by rewrite Ip.
    apply/mapP.
    have I: w \in [events of es1 | is_write & with_loc la].
    - move: wc; rewrite mem_filter wd /= /is_write /= /with_loc /= /loc /=.
    case: (lab es1 w)=> //= > /andP[/eqP->]; by rewrite eq_refl.
    exists (exist _ w I); first by rewrite seq_in_mem.
    apply/congr2=> /=; first (apply/congr1/of_add_label_inj=> /=);
    by rewrite /value /= (synch_val _ _ _ _ wc).
  1-3: move=>> <- /=-> [al -> Eal]; rewrite ?inE; apply/eqP;
  congr (_, _); apply/congr1/of_add_label_inj=> /=;
  rewrite -Eal; apply/congr1; case: al Eal=> /= ?? aw ??? /[swap][[<-?->]];
  rewrite /(_ \>> _); case: (lab es1 aw =P Init); last (by case: (lab _ _));
  by move/lab_Init.
  all: move=> E'; by rewrite E' eq_refl ?andbF in ni.
Qed.

Definition eqv := (@AddEvent.eqv disp E Val).

Lemma iso_swap l1 pr1 v1 l2 pr2 v2 es1 es2 es3:
  es1 ~(l1, pr1, v1)~> es2 ->
  es1 ~(l2, pr2, v2)~> es3 ->
  exists es4 es4',
    [/\ es2 ~(l2, pr2, v2)~> es4,
        es3 ~(l1, pr1, v1)~> es4' &
        AddEvent.is_iso (swap id (fresh_id1 es1) (fresh_id2 es1)) es4 es4'].
Proof.
  case/ltrP=> la1 [/AddEvent.iso_swap L ??? /ltrP[la2 [/L]]].
  case=> es4 [es4' [l*]]; exists es4, es4'.
  split=> //; apply/ltrP; by [exists la2| exists la1].
Qed.

Lemma comm_ltr l1 l2 : eqv_diamond_commute (ltr l1) (ltr l2) eqv.
Proof.
  move=> es1 ?? /iso_swap/[apply][[es4 [es4' [*]]]].
  by exists es4, es4'; split=> //; exists (swap id (fresh_id1 es1) (fresh_id2 es1)).
Qed.

Lemma iso_swap_eqv l1 pr1 v1 f g es1 es2 es3: 
  let: h := swap f (fresh_id1 es1) (g (fresh_id1 es3)) in
  es1 ~(l1, pr1, v1)~> es2 ->
  AddEvent.is_iso f es1 es3 -> 
  cancel g f -> 
  exists es4,
    [/\ es3 ~(l1, h pr1, v1)~> es4 &
        AddEvent.is_iso h es2 es4].
Proof.
  case/ltrP=> al [/AddEvent.iso_swap_eqv L H1 H2 H3 {L}/L/[apply]].
  set h := (swap f (fresh_id1 es1) (g (fresh_id1 es3))).
  case=> es4 [[al' -> Le ?]]; exists (add_event al'); split=> //.
  apply/ltrP; exists (edescr_map h al); split=> //.
  - by exists al'.
  - rewrite Le; by case: (al') (al) H1 Le=> /= > I ??? [/=> <- [?]].
  1,2: by move: H2 H3; case: (al).
Qed.

Lemma comm_eqv_tr :
  diamond_commute eqv tr.
Proof.
  move=> es1 es2 ?; rewrite (exlab_tr _ _)=> [[f /[dup] [[_ [g ? c I]]]]].
  set h := swap f (fresh_id1 es1) (g (fresh_id1 es2)).
  case=> [[[l pr v /iso_swap_eqv/(_ I c)[es4 [??]]]]].
  exists es4; last by exists h.
  by rewrite (exlab_tr _ _); exists (l, h pr, v).
Qed.

Lemma ltr_fresh es1 es2 l v pr :
  es1 ~(l, pr, v)~> es2 -> fresh_id2 es1 = fresh_id1 es2.
Proof. by move/ltrP=> [? [[? ->]]]. Qed.

Lemma ltr_dom es1 es2 l v pr :
  es1 ~(l, pr, v)~> es2 -> pr \in dom es1.
Proof. by rewrite /ltr /add_hole; case: eqP. Qed.

Lemma ltr_dom2 es1 es2 l v pr :
  es1 ~(l, pr, v)~> es2 -> dom es2 = fresh_id1 es1 :: dom es1.
Proof. by move/ltrP=> [? [[? ->]]]. Qed.

End AddHoleConfl.

End AddHole.

Module Prog.

Section ProgConfl.

Open Scope fmap_scope.
Open Scope do_notation.
Open Scope exec_eventstruct_scope.

Context {Val : inhType}.

Variable pgm : prog (Val := Val).

Definition ltr (l : (@Lab unit Val) * Val) st st' := 
  (l.1, st') \in [seq (x.1, x.2 l.2) | x <- prog_sem pgm st].

Notation "e1 '~(' l ',' v ')~>' e2" := (ltr (l, v) e1 e2) (at level 20).

Lemma Eps_det st st1 st2 v u l: 
  st ~(Eps, v)~> st1 ->
  st ~(l  , u)~> st2 ->
  ((st1 = st2) * (l = Eps))%type.
Proof.
  case: st=> /=; rewrite /ltr /==> ??; case: ifP=> //. 
  - move=> ? L; exfalso; move: L; by elim: (thrd_prositions pgm).
  by case: (nth Stop pgm _.-1)=> //= > ?; rewrite ?inE=> /eqP[-> /eqP [->]].
Qed.

End ProgConfl.

End Prog.

Module RegMachine.

Section RegMachineConfl.

Import Order.LTheory.

Open Scope fmap_scope.
Open Scope do_notation.
Open Scope exec_eventstruct_scope.
Open Scope order_scope.

Local Notation M := ModelMonad.ListMonad.t.

Context {disp} {E : identType disp} {Val : inhType}.

(*Notation n := (@n val).*)
Notation exec_event_struct := (fin_exec_event_struct E Val).
Notation cexec_event_struct := (cexec_event_struct E Val).

Variable pgm : prog (Val := Val).

Implicit Type c : @config disp E Val.

Notation eval_step := (eval_step pgm (disp := disp) (E := E)).
Notation Progltr := (Prog.ltr pgm).

Definition ltr pr (c c' : config) := c' \in eval_step c pr.

Notation "c1 '~(' pr ')~>' c2" := (ltr pr c1 c2) (at level 20).

Definition tr := exlab ltr.

Definition is_iso (f : E -> E) c c' := 
  AddEvent.is_iso f c c' /\ {in dom c, c =1 c' \o f}.

Lemma is_iso_id c : is_iso id c c.
Proof. split=> //; exact/AddEvent.is_iso_id. Qed.

Definition eqv := exlab is_iso.

Lemma eqvcc c : eqv c c.
Proof. exists id; exact/is_iso_id. Qed.

Lemma eqv_symm : Symmetric eqv.
Proof.
  move=> ?? [f [/[dup][[? [g /[dup] c1 /AddEvent.is_iso_can L /[dup]]]]]].
  move=> {L}/L L c2 /[dup] /L ? I D; exists g; split=> // x.
  rewrite -(AddEvent.iso_dom I) -{1}[x]c2 (mem_map (can_inj c1))=> /D /=.
  by rewrite c2.
Qed.

Lemma eqv_evstr c c': eqv c c' -> AddEvent.eqv c c'.
Proof. case=> f []; by exists f. Qed.

Definition silent_ltr pr c c' := 
  [/\ Progltr (Eps, inh) (c pr) (c' pr),
      pr \in dom c,
      [fsfun c with pr |-> c' pr] = c' &
      c = c' :> exec_event_struct].

Lemma silent_det c c1 c2 pr : 
  silent_ltr pr c c1 ->
  silent_ltr pr c c2 ->
  c1 = c2.
Proof.
  case=> /Prog.Eps_det L +++ [{L}/L<-].
  case: c1 c2=> /= e1 t1 [/= e2 t2 ? <-<- ? <-<-].
  by rewrite fsfun_with.
Qed.

Definition non_silent_ltr pr c c' := 
  exists l v, 
  [/\ Progltr (l, v) (c pr) (c' (fresh_id1 c)),
      l != Eps,
      [fsfun c with fresh_id1 c |-> c' (fresh_id1 c)] = c' &
      AddHole.ltr (l, pr, v) c c'].

Lemma non_silent_dom pr c c' : 
  non_silent_ltr pr c c' -> pr \in dom c.
Proof. by case=> ? [? [??? /AddHole.ltr_dom]]. Qed.

Lemma silent_dom pr c c' : 
  silent_ltr pr c c' -> pr \in dom c.
Proof. by case. Qed.

Lemma ltrP c c' pr : 
  reflect (silent_ltr pr c c' \/ non_silent_ltr pr c c')
    (c ~(pr)~> c').
Proof.
  apply: (iffP idP); rewrite /ltr /eval_step.
  - case: ifP=> D //.
    have: forall v l st, 
      (l, st) \in [seq (x.1, x.2 v) | x <- prog_sem pgm (c pr)] ->
      Progltr (l, v) (c pr) st by [].
    elim: (prog_sem pgm (c pr))=> //=.
    move=> [l cont /= conts] IHp H; rewrite do_cons mem_cat=> /orP[].
    - move: H; case: (l =P Eps)=> /= [->/(_ inh Eps (cont inh) (mem_head _ _))|].
      - rewrite ?inE=> P /eqP->; left.
        split=> //=; by rewrite fsfun_with.
      move=> /eqP ? H /do_mem[[es v ?]].
      rewrite ?inE=> /eqP->; right; exists l, v.
      split=> //=; rewrite ?fsfun_with //; exact/H/mem_head.
    by apply/IHp=> ??? I; apply/H; rewrite ?inE I.
  have H: forall v l st, Progltr (l, v) (c pr) st ->
    (l, st) \in [seq (x.1, x.2 v) | x <- prog_sem pgm (c pr)] by [].
  case: ifP=> [?|/[swap][[/silent_dom|/non_silent_dom]]->] //.
  case=> [|[l[v]]][]; rewrite /Prog.ltr /=; 
  elim: (prog_sem pgm (c pr))=> //= [][la cont ? /=];
  rewrite do_cons mem_cat; move=> IHp.
  - rewrite ?inE=> /orP[/eqP|/IHp/[apply]/[apply]/[apply]->//].
    case=><-->; rewrite eq_refl /= ?inE /eq_op /= /eq_config /==>?<-<-;
    by rewrite ?eq_refl.
  rewrite ?inE=> /orP[/eqP[->+->]|/IHp/[apply]/[apply]/[apply]->//].
  move=> E1 E2 ?. apply/orP; left; apply/do_mem; exists (evstr c', v)=> //.
  by rewrite ?inE /eq_op /= /eq_config /= -E1 E2 ?eq_refl. 
Qed.

Lemma rltrP c c' pr : 
  ((1 + (silent_ltr pr : hrel _ _))%ra c c' \/
   (1 + (non_silent_ltr pr : hrel _ _))%ra c c') <->
  ((1 + (ltr pr : hrel _ _))%ra c c').
Proof.
  split=> [[|][->|]|[->|/ltrP[]]] *; try by (right + left).
  - by right; apply/ltrP; left.
  - by right; apply/ltrP; right.
  all: by do ? (left + right).
Qed.

Lemma comm_nnltr {pr1 pr2}:
  eqv_rdiamond_commute (non_silent_ltr pr1) (non_silent_ltr pr2) eqv.
Proof.
  apply/diamond_rdiamod.
  move=> c1 c2 c3 [l [v [?? E1 /[dup]/AddHole.ltr_fresh fr ]]].
  move=> /[dup]/AddHole.ltr_dom I1 /AddHole.iso_swap L [m [u [?? E2]]].
  move=> /[dup]/AddHole.ltr_fresh fr' /[dup] /AddHole.ltr_dom I2 {L}/L.
  case=> es4 [es4' [???]].
  have N: (fresh_id1 c1) == (fresh_id2 c1) = false.
  - by apply/negbTE/eqP=> /(@fresh_iter _ _ 1 2).
  exists (Config es4  [fsfun c2 with fresh_id2 c1 |-> c3 (fresh_id1 c1)]),
         (Config es4' [fsfun c3 with fresh_id2 c1 |-> c2 (fresh_id1 c1)]).
  split=> /=.
  - exists m, u; split=> //=; rewrite -?fr fsfun_with //.
    rewrite -E1 fsfun_withE (lt_eqF (fresh_seq_lt dom_sorted I2)) //.
  - exists l, v; split=> //=; rewrite -?fr' ?fsfun_with //.
    rewrite -E2 fsfun_withE (lt_eqF (fresh_seq_lt dom_sorted I1)) //.
  exists (swap id (fresh_id1 c1) (fresh_id2 c1)); split=> //= x.
  rewrite -E1 -E2 /=; rewrite fsfun_withE; case: ifP=> [/eqP->|N1].
  - rewrite swap2 ?fsfun_withE eq_refl N //.
  rewrite fsfun_withE; case: ifP=> [/eqP->|N2].
  - by rewrite swap1 ?fsfun_with.
  by rewrite -swap_not_eq // ?fsfun_withE ?(N1, N2).
Qed.

Lemma comm_ssltr {pr1 pr2}: 
  eqv_rdiamond_commute (silent_ltr pr1) (silent_ltr pr2) eqv.
Proof.
  move=> c1 c2 c3.
  case: (pr1 =P pr2)=> [-> /silent_det/[apply]->|/eqP/negbTE N].
  - exists c3, c3; split; last (exact/eqvcc); by left.
  case=> [? D1 C1 E1 [? D2 C2 E2]].
  exists (Config c2 [fsfun c2 with pr2 |-> c3 pr2]),
         (Config c3 [fsfun c3 with pr1 |-> c2 pr1]).
  split; rewrite -1?C1 -1?C2 ?fsfun_with.
  - right; split=> //=; rewrite -?E1 // fsfun_with //.
    - rewrite -C1 fsfun_withE eq_sym N //.
    by rewrite -{1}C1.
  - right; split=> //=; rewrite -?E2 // fsfun_with //.
    - rewrite -C2 fsfun_withE N //.
    by rewrite -{1}C2.
  exists id; rewrite -E1 -E2; split=> /=; first exact/AddEvent.is_iso_id.
  move=> ?; rewrite /= ?fsfun_withE; case: ifP=> [/eqP->|//].
  by rewrite eq_sym N.
Qed.

Lemma comm_nsltr {pr1 pr2}: 
  eqv_rdiamond_commute (non_silent_ltr pr1) (silent_ltr pr2) eqv.
Proof.
  apply/diamond_rdiamod.
  move=> c1 c2 c3 [l [v [p1 N C1 L [p2 I2 C2 Ec]]]].
  do ? exists (Config c2 
          [fsfun c1 with pr2          |-> c3 pr2,
                         fresh_id1 c1 |-> c2 (fresh_id1 c1)]).
  split=> //=; last exact/eqvcc.
  - split=> //=. 
    - rewrite -{1}C1 ?fsfun_withE eq_refl; case: ifP=> //.
      by rewrite (lt_eqF (fresh_seq_lt dom_sorted I2)).
    - by rewrite (AddHole.ltr_dom2 L) ?inE I2.
    by rewrite fsfun_with -{1}C1.
  exists l, v; split=> //=; rewrite -?Ec // ?fsfun_withE.
  - rewrite eq_refl eq_sym (lt_eqF (fresh_seq_lt dom_sorted I2)).
    rewrite -C2 fsfun_withE.
    by case: ifP p2 p1 N=> // /eqP-> /Prog.Eps_det/[apply]->.
  rewrite eq_refl eq_sym ((lt_eqF (fresh_seq_lt dom_sorted I2))).
  rewrite -{1}C2; apply/fsfunP=> ?; rewrite ?fsfun_withE.
  case: ifP=> // /eqP->. 
  by rewrite eq_sym ((lt_eqF (fresh_seq_lt dom_sorted I2))).
Qed.

Lemma comm_ltr pr1 pr2 : eqv_rdiamond_commute (ltr pr1) (ltr pr2) eqv.
Proof.
  move=> ??? /ltrP[] t1 /ltrP[] t2.
  - case: (comm_ssltr t1 t2)=> s4 [s4' [*]].
  2: case: ((comm_nsltr t2 t1))=> s4' [s4 [?? /eqv_symm ?]]. 
  3: case: (comm_nsltr t1 t2)=> s4 [s4' [*]].
  4: case: (comm_nnltr t1 t2)=> s4 [s4' [*]].
  all: exists s4, s4'; split=> //; apply/rltrP; by (left + right). 
Qed.

Lemma comm_tr_eqv : diamond_commute eqv tr.
Proof.
  move=> c1 c3 c2 /[swap][] [pr T].
  have In : pr \in dom c1 by move: T; rewrite /ltr /eval_step; case: ifP.
  case/ltrP: T=> [[?? T C [f [/[dup] L [_ b] C1]]]|].
  - exists (Config c3 [fsfun c3 with f pr |-> c2 pr]).
  - exists (f pr); apply/ltrP; left; split=> //=.
    - move: (C1 _ In)=> /=<-. by rewrite fsfun_with.
    - rewrite -(AddEvent.iso_dom L) mem_map //; exact/bij_inj.
      by rewrite fsfun_with.
    exists f; split=> //= [|?]; rewrite -C // => D.
    rewrite /= -T ?fsfun_withE eq_refl (bij_eq b).
    by move: (C1 _ D)=> /=->.
  case=> l [v [?? E1 /[dup] T /AddHole.iso_swap_eqv L]].
  case=> [f /[dup][[/[dup] Is[? /[dup] bf [g c' c _]]]]] [] /L/(_ c)[es4 []].
  set h := swap f (fresh_id1 c1) (g (fresh_id1 c3))=> ?? /[dup]C /(_ pr) /= Eq.
  exists (Config es4 [fsfun c3 with fresh_id1 c3 |-> c2 (fresh_id1 c1)]). 
  - exists (h pr); apply/ltrP; right; exists l, v; split=> //=.
    - rewrite fsfun_with /h -swap_not_eq -?Eq //; apply/eqP; move: In=> /[swap].
      - by move->=>/(negP (fresh_seq_notin dom_sorted)).
      move->; rewrite -[dom c1](mapK c') mem_map; last exact/can_inj.
      by rewrite (AddEvent.iso_dom Is)=> /(negP (fresh_seq_notin dom_sorted)).
    by rewrite fsfun_with.
  exists h; split=> // x /=; rewrite -{1}E1 /h /swap fsfun_withE.
  case: ifP=> [|]; first rewrite c fsfun_with //.
  have D: dom c2 = fresh_id1 c1 :: dom c1 by apply/(AddHole.ltr_dom2 T).
  case: ifP=> [/eqP->|N1]; rewrite D ?inE=>-> /=.
  - rewrite -[dom c1](mapK c') mem_map; last exact/can_inj.
    by rewrite (AddEvent.iso_dom Is)=> /(negP (fresh_seq_notin dom_sorted)).
  by move/C=> /=->; rewrite fsfun_withE -[fresh_id1 _]c (bij_eq bf) N1.
Qed.

Theorem ltr_confl : eqv_rconfluent tr eqv.
Proof.
  apply/(eqv_comm_union _ _ _ eqv_symm _ comm_ltr comm_tr_eqv).
  - move=> ??? [f [L1 D1 [g [L2 D2]]]]; exists (g \o f); split.
    - exact/(AddEvent.is_iso_comp L1 L2).
    move=> ? /[dup] D /D1 /=->; apply/D2.
    rewrite -(AddEvent.iso_dom L1) mem_map //; exact/bij_inj/(L1.2).
  move=> ??->; exact/eqvcc.
Qed.

End RegMachineConfl.

End RegMachine.






