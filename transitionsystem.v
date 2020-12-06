From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order.
From mathcomp Require Import eqtype fingraph path finmap. 
From event_struct Require Import utilities relations ident rfsfun.
From event_struct Require Import eventstructure.

(******************************************************************************)
(* Here we want to make function that by event and event structure creates a  *)
(* new event structure with added event. Than we want to describe behavior of *)
(* ca, cf, ... on new sructure in terms of ca, cf, ... on old one. Finally we *)
(* we want to proof that if our structure is consisten, and we are adding the *)
(* element that is bot conflicting with his predsessors, than our new         *)
(* stucture is going to be consistent, too.                                   *)
(*                                                                            *)
(* This file contains the definitions of:                                     *)
(*         add_label == special record with all nesessary information about   *)
(*                   event that we want to add to a fin_exec_event_structure  *)
(*         add_event es al == function that takes fin_exec_event_structure    *)
(*                   and record add_label with event we want to add and       *)
(*                   returns new fin_exec_event_structure with added element  *)
(*         'function'_add_eventE == lemma that determines behavior of         *)
(*                   'function' on the new event structure with added element *)
(*                    in terms of 'function' on event structure without one   *)
(*         consist_add_event == statement about consistance of our new        *)
(*                    structure                                               *)
(*         tr_add_event e1 e2 == we can add some event to e1 and obtain e2    *)
(*         ltr_add_event e1 al e2 == we can add al to e1 and obtain e2        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.LTheory.
Open Scope order_scope.

Section TransitionSystem.

Context {val : eqType} {disp} (E : identType disp).

Notation exec_event_struct := (@fin_exec_event_struct val disp E).
Notation cexec_event_struct := (@cexec_event_struct val disp E).

Notation label := (@label val val).

Implicit Types (x : loc) (a : val) (es : exec_event_struct).

(* Section with definitions for execution graph with added event *)
Section AddEvent.

(* execution graph in which we want to add l *)
Context (es : exec_event_struct).

Notation dom := (dom es).
Notation lab    := (lab es).
Notation ffpred  := (ffpred es).
Notation ffrf    := (ffrf es).
Notation fresh := (fresh_seq dom).

Definition wr (lab : E -> label) := 
  [rel r w : E | (w <= r) &&
  (((w == r) && (~~ is_read (lab r))) || ((lab w) << (lab r)))].

Structure add_label :=
  Add {
    add_lb            : label;

    add_pred          : E;
    add_pred_in_dom   : add_pred \in fresh :: dom;

    add_write         : E;
    add_write_in_dom  : add_write \in fresh :: dom;
    add_write_consist : ((add_write == fresh) && (~~ is_read add_lb)) ||
                        ((lab add_write) << add_lb);
}.

Variable al : add_label.

(* label of an event which we want to add     *)
Notation lb := (add_lb al). 

(* predecessor of the new event (if it exists) *)
Notation pred := (add_pred al).

(* if event is `Read` then we should give `Write` from wich we read *)
Notation write := (add_write al).

Definition add_lab := add_rfsfun fresh lb erefl lab.

Definition add_ffpred :=
  add_rfsfun fresh pred (fresh_seq_le (dom_sorted es) (add_pred_in_dom al)) ffpred.

Lemma add_lab_write_read: wr add_lab fresh write.
Proof.
  move: (add_write_consist al).
  rewrite /add_lab /= ?fsfun_with fsfun_withE.
  case: ifP=> /= [/eqP->|?->]; first by rewrite lab_fresh /= orbF lexx=>->.
  by move/(fresh_seq_le (dom_sorted es)): (add_write_in_dom al)=>->.
Qed.

Lemma add_lab_write_read_i: 
  all (fun r => wr lab r (ffrf r) ==> wr add_lab r (ffrf r)) dom.
Proof.
  apply/allP=> x.
  rewrite /add_lab /= ?fsfun_withE => /(fresh_seq_lt (dom_sorted es)).
  case X: (ffrf x <= x)=> //= /dup /le_lt_trans; move/(_ _ X).
  case: ifP=> [/eqP->|?]; first by rewrite lt_irreflexive.
  case: ifP=> [/eqP->|]; by rewrite (lt_irreflexive, implybb).
Qed.

Definition add_ffrf := 
  @add_rfsfun _ _ _ _ (wr add_lab)
  fresh write add_lab_write_read
  (rfsfun_impl add_lab_write_read_i).

Definition add_event := 
  @Pack _ _ _ (fresh :: dom) (path_fresh_seq (dom_sorted es)) add_lab add_ffpred add_ffrf.

Hypothesis consist : consistency es.
Hypothesis ncf_rf : ~~ (cf add_event fresh write).

Arguments cfP {_ _ _ _}.
Import Relation_Operators.

Lemma fpred_add_eventE e : fpred add_event e = 
  if e == fresh then pred else fpred es e.
Proof. by rewrite /fpred /add_event /= fsfun_withE. Qed.

Lemma frf_add_eventE e : frf add_event e =
  if e == fresh then write else frf es e.
Proof. by rewrite /frf /add_event /= fsfun_withE. Qed.

Lemma ica_add_eventE e1 e2: 
  ica add_event e1 e2 =
  if e2 == fresh then 
    (pred == e1) || (write == e1)
  else ica es e1 e2.
Proof.
  rewrite /ica /fica frf_add_eventE fpred_add_eventE.
  by case: ifP=> ?; rewrite ?(andTb, andFb) ?orbF // ?inE eq_sym orbC eq_sym.
Qed.

Lemma ica_fresh e: ica es fresh e -> e = fresh.
Proof.
  move/dup/fica_ca/ca_codom/swap/fica_le.
  rewrite /ica ?inE. 
  case I: (e \in dom); last by move=> ?/(_ erefl)/eqP->.
  by move/lt_geF: (fresh_seq_lt (dom_sorted es) I)=>->.
Qed.

Lemma ca_fresh e: ca es fresh e -> e = fresh.
Proof. by move/closureP; elim=> // ?? /swap ? /swap-> /ica_fresh. Qed.

Lemma ca_add_eventE e1 e2: e2 != fresh -> ca es e1 e2 = ca add_event e1 e2.
Proof.
  move=> N.
  apply (refleqP (closureP _ _ _) (closureP _ _ _)).
  split; move: N=> /swap; elim; try constructor.
  all: move=> y ? I ? H /negbTE Z; apply (rtn1_trans _ _ _ y)=> //.
  2,4: apply/H/negP; move: I.
  - by rewrite ica_add_eventE Z.
  - move/swap/eqP=>->/ica_fresh Ez.
    by move/eqP: Z Ez.
  - rewrite ica_add_eventE Z=> /swap/eqP->/ica_fresh.
    by move/eqP: Z.
  move: I; by rewrite ica_add_eventE Z.
Qed.

Lemma icf_add_eventE e1 e2 :
  e1 != fresh -> e2 != fresh ->
  icf es e1 e2 = icf add_event e1 e2.
Proof.
  by rewrite /icf !fpred_add_eventE /= ?fsfun_withE => /negbTE->/negbTE->.
Qed.

Lemma cf_add_eventE e1 e2:
  e1 != fresh -> e2 != fresh ->
  cf es e1 e2 = cf add_event e1 e2.
Proof.
  move=> /dup ? /negP N1 /dup ? /negP N2.
  apply: (refleqP (cfP _ _ ) (cfP _ _)). 
  apply /exists_eq => x; apply /exists_eq=> y.
  rewrite -?ca_add_eventE //. 
  apply /Bool.eq_iff_eq_true/and_eq => C; apply /and_eq=> ?.
  rewrite icf_add_eventE //; apply/eqP=> Eq.
  - apply/N1/eqP/ca_fresh; by rewrite -Eq.
  apply/N2/eqP/ca_fresh; by rewrite -Eq.
Qed.

Lemma consist_add_event: consistency add_event.
Proof.
  rewrite /consistency; apply /allP=> e1.
  rewrite /add_event /frf /= fsfun_withE ?inE.
  case: ifP=> /= [/eqP->|/negbT N /(allP consist)] //.
  rewrite -cf_add_eventE //.
  apply/negP=> /eqP Ef.
  have /ica_fresh /eqP /(negP N) //: ica es fresh e1.
  by rewrite /ica ?inE -Ef eq_refl.
Qed.

End AddEvent.

Definition tr_add_event es1 es2 := exists al, es2 = @add_event es1 al.

Notation "es1 '-->' es2" := (tr_add_event es1 es2) (at level 0).

Definition ltr_add_event es1 al es2 := es2 = @add_event es1 al.

Notation "es1 '--' al '-->' es2" := (ltr_add_event es1 al es2) (at level 0).

End TransitionSystem.