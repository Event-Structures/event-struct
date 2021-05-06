From RelationAlgebra Require Import lattice monoid rel kat_tac kleene.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice seq path.
From mathcomp Require Import order finmap fintype ssrnat.
From event_struct Require Import utilities eventstructure ident.
From event_struct Require Import rewriting_system.

(******************************************************************************)
(* Here we want to make function that by event and event structure creates a  *)
(* new event structure with added event. Then we want to describe behavior of *)
(* ca, cf, ... on new sructure in terms of ca, cf, ... on old one. Finally we *)
(* we want to prove that if our structure is consisten, and we are adding the *)
(* element that is not conflicting with his predsessors, than our new         *)
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
(*         add_label_of_Nread == takes non-read label and predcessor and      *)
(*                    returns corresponding add_label structure               *)
(*         consist_Nread == lemma that ensures consistency of event structures*)
(*                    obtained by add_label_of_Nread                          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.LTheory.
Open Scope order_scope.
Open Scope fset_scope.

Definition add_wr {E V : eqType} e1 e2 (lab : E -> @label V V) l :=
  (e1 == e2) && (~~ is_read l) || ((lab e1) << l).

Arguments add_wr /.

Section TransitionSystem.

Context {V : eqType} {disp} (E : identType disp).

Notation exec_event_struct := (@fin_exec_event_struct V disp E).
Notation cexec_event_struct := (@cexec_event_struct V disp E).

Notation label := (@label V V).

Implicit Types (x : loc) (a : V) (es : exec_event_struct).

(* Section with definitions for execution graph with added event *)
Section AddEvent.

(* execution graph in which we want to add l *)
Context (es : exec_event_struct).

Notation dom := (dom es).
Notation flprf := (lprf es).
Notation flab := (lab es).
Notation ffpred := (fpred es).
Notation ffrf := (frf es).
Notation fresh_id := (fresh_seq dom).

Definition wr (lab : E -> label) :=
  [rel r w : E | (w <= r) && add_wr w r lab (lab r)].

Structure add_label := Add {
  add_lb            : label;

  add_pred          : E;
  add_pred_in_dom   : add_pred \in fresh_id :: dom;

  add_write         : E;
  add_write_in_dom  : add_write \in fresh_id :: dom;
  add_write_consist : add_wr add_write fresh_id flab add_lb;
}.


Fact add_write_consist_of_fresh l : ~~ is_read l ->
  add_wr fresh_id fresh_id flab l.
Proof. by move=> /= ->; rewrite eq_refl lab_fresh. Qed.

Definition add_label_of_Nread l {p}
           (p_mem : p \in fresh_id :: dom) (nr : ~~ is_read l) : add_label :=
  Add
    p_mem
    (mem_head fresh_id dom)
    (add_write_consist_of_fresh nr).

Variable al : add_label.

(* label of an event to add *)
Notation lb := (add_lb al).

(* predecessor of the new event (if it exists) *)
Notation pred := (add_pred al).

(* if our event is `Read` then we should provide the corresponding `Write`
   event *)
Notation write := (add_write al).

Definition add_lprf :=
  [ fsfun flprf with fresh_id |->
                    {| lab_prj := lb; fpred_prj := pred; frf_prj := write |} ].

Definition add_lab := fun e : E => lab_prj (add_lprf e).
Definition add_fpred := fun e : E => fpred_prj (add_lprf e).
Definition add_frf := fun e : E => frf_prj (add_lprf e).

Fact add_lprf_finsupp : finsupp add_lprf `<=` seq_fset tt (fresh_id :: dom).
Proof.
  apply/fsubsetP=> e; rewrite (@seq_fsetE tt).
  rewrite /add_lprf finsupp_with inE.
  case: ifP=> _; first by rewrite in_fsetD1; case/andP=> _ /lprf_dom ->.
  by case/fset1UP=> [->|/lprf_dom->//]; rewrite eqxx.
Qed.

Fact add_fpred_le : 
  [forall e : finsupp add_lprf, add_fpred (val e) <= val e].
Proof.
  apply/forallP=> [[/=]] e ?.
  rewrite /add_fpred /add_lprf fsfun_withE.
  case: (eqVneq e fresh_id)=> /= [->|]; last by rewrite fpred_le.
  by rewrite fresh_seq_le ?dom_sorted // (add_pred_in_dom al).
Qed.

Fact add_frf_le : 
  [forall e : finsupp add_lprf, add_frf (val e) <= val e].
Proof.
  apply/forallP=> [[/=]] e ?.
  rewrite /add_frf /add_lprf fsfun_withE.
  case: (eqVneq e fresh_id)=> /= [->|]; last by rewrite frf_le.
  by rewrite fresh_seq_le ?dom_sorted // (add_write_in_dom al).
Qed.

Fact add_frf_prop :
  [forall rs : seq_fset tt (fresh_id :: dom),
    let r := val rs in
    let w := add_frf r in
    (w == r) && ~~ is_read (add_lab r) || (add_lab w) << (add_lab r)].
Proof.
  apply/forallP=> [[r /=]]; rewrite (@seq_fsetE tt)=> ?.
  rewrite /add_frf /add_lab /add_lprf !fsfun_withE /=.
  case: (eqVneq r fresh_id)=> /= [->|_].
  - move: (add_write_consist al); rewrite /add_wr.
    case: (eqVneq write fresh_id)=> /= [|+]->.
    - by rewrite lab_fresh orbF=>->.
    by rewrite ?dom_sorted // (add_write_in_dom al).
  rewrite -?(labE,fpredE,frfE); move: (frf_cond es r); case/orP=> [->//|].
  by case: (eqVneq (ffrf r) fresh_id)=> [|_]->//; rewrite lab_fresh.
Qed.

Definition add_event :=
  @Pack _ _ _
        (fresh_id :: dom)
        (path_fresh_seq (dom_sorted es))
        add_lprf
        add_lprf_finsupp
        add_fpred_le
        add_frf_le
        add_frf_prop.

Hypothesis consist : dom_consistency es.
Hypothesis ncf_rf : ~~ (cf add_event fresh_id write).

Import Relation_Operators.

Lemma lprf_add_eventE e :
  lprf add_event e = if e == fresh_id then Lprf lb pred write else lprf es e.
Proof. by rewrite /add_event /= fsfun_withE /=; case: ifP. Qed.

Lemma lab_add_eventE e :
  lab add_event e = if e == fresh_id then lb else lab es e.
Proof. by rewrite /lab /add_event /= fsfun_withE /=; case: ifP. Qed.

Lemma fpred_add_eventE e :
  fpred add_event e = if e == fresh_id then pred else fpred es e.
Proof. by rewrite /fpred /add_event /= fsfun_withE /=; case: ifP. Qed.

Lemma frf_add_eventE e :
  frf add_event e = if e == fresh_id then write else frf es e.
Proof. by rewrite /frf /add_event /= fsfun_withE; case: ifP. Qed.

Lemma ica_add_eventE e1 e2 :
  ica add_event e1 e2 =
  if e2 == fresh_id then
    (pred == e1) || (write == e1)
  else ica es e1 e2.
Proof.
  rewrite /ica /fica frf_add_eventE fpred_add_eventE.
  by case: ifP=> ?; rewrite ?(andTb, andFb) ?orbF // ?inE eq_sym orbC eq_sym.
Qed.

Lemma ca_add_eventE e1 e2 :
  e2 != fresh_id -> ca es e1 e2 = ca add_event e1 e2.
Proof.
  move=> N.
  apply/closure_n1P/closure_n1P; move: N=> /[swap]; elim; try constructor.
  all: move=> y ? I ? H /negbTE Z; apply: (@rtn1_trans _ _ _ y).
  2,4: apply/H/negP; move: I.
  - by rewrite ica_add_eventE Z.
  - move/[swap]/eqP=>->/ica_fresh Ez.
    by move/eqP: Z Ez.
  - rewrite ica_add_eventE Z=> /[swap]/eqP->/ica_fresh.
    by move/eqP: Z.
  move: I; by rewrite ica_add_eventE Z.
Qed.

Lemma icf_add_eventE e1 e2 :
  e1 != fresh_id -> e2 != fresh_id ->
  icf es e1 e2 = icf add_event e1 e2.
Proof. by rewrite /icf !fpred_add_eventE=> /negbTE->/negbTE->. Qed.

Lemma cf_add_eventE e1 e2:
  e1 != fresh_id -> e2 != fresh_id ->
  cf es e1 e2 = cf add_event e1 e2.
Proof.
  move=> /[dup] /ca_fresh_contra Cnf1 Nf1 /[dup] /ca_fresh_contra Cnf2 Nf2.
  apply/cfP/cfP=> -[x [y C]]; exists x, y; move: C; rewrite -?ca_add_eventE //.
  - move=> C; rewrite -icf_add_eventE //; first by rewrite Cnf1 ?C.
    by rewrite Cnf2 ?C.
  move=> C; rewrite icf_add_eventE //; first by rewrite Cnf1 ?C.
  by rewrite Cnf2 ?C.
Qed.

Lemma consist_add_event: dom_consistency add_event.
Proof.
  rewrite /dom_consistency; apply /allP=> e1.
  rewrite /frf /= fsfun_withE ?inE.
  case: ifP=> /= [/eqP-> _|/negbT N /(allP consist)] //; first exact/implyP.
  rewrite -cf_add_eventE //.
  apply/negP=> /eqP Ef.
  have /ica_fresh /eqP /(negP N) //: ica es fresh_id e1.
  by rewrite /ica ?inE -Ef eq_refl.
Qed.

End AddEvent.

Section Nread_Consist.

Context (ces : cexec_event_struct) (pr : E) (l : label).

Notation domain := (dom ces).
Notation fresh_id := (fresh_seq domain).

Hypothesis nr     : ~~ is_read l.
Hypothesis pr_mem : pr \in fresh_id :: domain.

Lemma consist_Nread:
   dom_consistency (add_event (add_label_of_Nread pr_mem nr)).
Proof.
  apply/consist_add_event=> //; first by case: ces.
  set ae := add_event (add_label_of_Nread pr_mem nr).
  rewrite cf_irrelf // /dom_consistency /=.
  apply/andP; split; first by rewrite frf_add_eventE /= ?eq_refl.
  apply/allP => x I; suff N: x != fresh_id.
  rewrite -cf_add_eventE // frf_add_eventE (negbTE N).
  - by case: ces I=> /= ? /allP /[apply].
  - move/(le_lt_trans (frf_le ces x)): (fresh_seq_lt (dom_sorted ces) I).
    apply/contraL=> /eqP->; by rewrite ltxx.
  move: (fresh_seq_lt (dom_sorted ces) I); apply/contraL=> /eqP->.
  by rewrite ltxx.
Qed.

End Nread_Consist.

Definition tr_add_event es1 es2 := exists al, es2 = @add_event es1 al.

Notation "es1 '-->' es2" := (tr_add_event es1 es2) (at level 0).

Definition ltr_add_event es1 al es2 := es2 = @add_event es1 al.

Notation "es1 '--' al '-->' es2" := (ltr_add_event es1 al es2) (at level 0).

End TransitionSystem.

