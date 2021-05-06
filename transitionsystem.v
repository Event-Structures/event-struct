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
(*         contain al es == checks if event that we want to add (al) is       *)
(*                    already in es                                           *)
(*         add_new_event == adding a new event to the event structrure if it  *)
(*                    is not contained there                                  *)
(*         consist_add_new_event == statement about consistance of our new    *)
(*                    structure obtained with add_new_event                   *)
(*         consist_new_Nread== lemma that ensures consistency of event        *)
(*                structures obtained by add_label_of_Nread of a new event    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.LTheory.
Open Scope order_scope.
Open Scope fset_scope.

Import Label.Syntax.

Definition add_wr {E V : eqType} e1 e2 (lab : E -> @Lab V V) l :=
  (e1 == e2) && (~~ Label.is_read l) || ((lab e1) \>> l).

Arguments add_wr /.
Arguments dom0 {_ _ _ _}.

Section TransitionSystem.

Context {disp} (E : identType disp) (V : eqType).

Notation exec_event_struct := (@fin_exec_event_struct disp E V).
Notation cexec_event_struct := (@cexec_event_struct disp E V).

Notation label := (@Lab V V).

Implicit Types (x : Loc) (a : V) (es : exec_event_struct).

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
  add_write         : E;

  add_pred_in_dom   : add_pred \in dom;
  add_write_in_dom  : add_write \in dom;
  add_write_consist : add_wr add_write ident0 flab add_lb;
}.

Coercion of_add_label := fun
  '(Add l p w _ _ _) => Lprf l p w.

Lemma of_add_label_inj: injective of_add_label.
Proof.
  case=> ??? +++ [??? +++ [le pe we]].
  move: le pe we; (do ? case :_ /)=> *; congr Add; exact/eq_irrelevance.
Qed.

Fact add_write_consist_of_fresh l : ~~ Label.is_read l ->
  add_wr ident0 ident0 flab l.
Proof. by move=> /= ->; rewrite eq_refl lab0. Qed.

Definition add_label_of_Nread l {p}
           (p_mem : p \in dom) (nr : ~~ Label.is_read l) : add_label :=
  Add
    p_mem
    dom0
    (add_write_consist_of_fresh nr).

Variable al : add_label.

(* label of an event to add *)
Notation lb := (add_lb al).

(* predecessor of the new event (if it exists) *)
Notation pred := (add_pred al).

(* if our event is `Read` then we should provide the corresponding `Write`
   event *)
Notation write := (add_write al).

Lemma pred_fresh_id: pred < fresh_id.
Proof. by move/add_pred_in_dom/(fresh_seq_lt dom_sorted): al. Qed.

Lemma write_fresh_id: write < fresh_id.
Proof. by move/add_write_in_dom/(fresh_seq_lt dom_sorted): al. Qed.

Definition contain := 
  has (fun e => (flab e == lb) && (ffrf e == write) && (ffpred e == pred)) dom.

Definition add_lprf :=
  [ fsfun flprf with fresh_id |->
                    {| lab_prj := lb; fpred_prj := pred; frf_prj := write |} ].

Definition add_lab := fun e : E => lab_prj (add_lprf e).
Definition add_fpred := fun e : E => fpred_prj (add_lprf e).
Definition add_frf := fun e : E => frf_prj (add_lprf e).

Arguments ident0_fresh {_ _ _ _}.

Fact add_lprf_finsupp : finsupp add_lprf == (seq_fset tt (fresh_id :: dom) `\ ident0).
Proof.
  apply/fset_eqP=> x; rewrite ?inE seq_fsetE finsupp_with.
  case: ifP; rewrite ?inE lprf_dom // mem_filter.
  - move: pred_fresh_id=> /[swap]/eqP[?->]; by rewrite ltxx.
  case: (x =P fresh_id)=> //=-> ?; rewrite andbT eq_sym.
  exact/esym/negbT/lt_eqF/ident0_fresh.
Qed.

Fact add_fpred_le : 
  [forall e : finsupp add_lprf, add_fpred (val e) < val e].
Proof.
  apply/forallP=> [[/=]] e; rewrite (eqP add_lprf_finsupp) ?inE seq_fsetE ?inE.
  rewrite /add_fpred /add_lprf fsfun_withE; case: ifP=> /= [/eqP-> _|??].
  - exact/pred_fresh_id.
  by apply/fpred_dom_lt; rewrite lprf_dom mem_filter.
Qed.

Fact add_frf_le : 
  [forall e : finsupp add_lprf, add_frf (val e) < val e].
Proof.
  apply/forallP=> [[/=]] e; rewrite (eqP add_lprf_finsupp) ?inE seq_fsetE ?inE.
  rewrite /add_frf /add_lprf fsfun_withE; case: ifP=> /= [/eqP-> _|??].
  - exact/write_fresh_id.
  by apply/frf_dom_lt; rewrite lprf_dom mem_filter.
Qed.

Fact add_frf_prop :
  [forall rs : seq_fset tt (fresh_id :: dom),
    let r := val rs in
    let w := add_frf r in
    (w == ident0) && ~~ Label.is_read (add_lab r) || (add_lab w) \>> (add_lab r)].
Proof.
  apply/forallP=> [[r /=]]; rewrite (@seq_fsetE tt).
  rewrite /add_frf /add_lab /add_lprf !fsfun_withE /= ?inE.
  case: ifP=> /= [/eqP|?/[dup]/frf_cond /[swap]].
  - case: ifP=> [/eqP|*]; last exact/add_write_consist.
    - move/lt_eqF/eqP: write_fresh_id; exact.
  by move/(fresh_seq_lt dom_sorted)/(le_lt_trans (frf_le _ _))/lt_eqF->.
Qed.

Lemma Nfresh_dom0: 
  ident0 \in fresh_id :: dom.
Proof. by rewrite ?inE dom0. Qed.

Definition add_event :=
  @Pack _ _ _
        (fresh_id :: dom)
        add_lprf
        (path_fresh_seq dom_sorted)
        Nfresh_dom0
        add_lprf_finsupp
        add_fpred_le
        add_frf_le
        add_frf_prop.

Definition add_new_event := if contain then es else add_event.

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
  rewrite icaE /= /fica frf_add_eventE fpred_add_eventE.
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
  by rewrite icaE /= ?inE -Ef eq_refl.
Qed.

Lemma consist_add_new_event: dom_consistency add_new_event.
Proof. rewrite /add_new_event; case: ifP=> // _; exact: consist_add_event. Qed.

End AddEvent.

Section Nread_Consist.

Context (ces : cexec_event_struct) (pr : E) (l : label).

Notation domain := (dom ces).
Notation fresh_id := (fresh_seq domain).

Hypothesis nr     : ~~ Label.is_read l.
Hypothesis pr_mem : pr \in domain.

Lemma consist_Nread:
   dom_consistency (add_event (add_label_of_Nread pr_mem nr)).
Proof.
  apply/consist_add_event=> //; first by case: ces.
  set ae := add_event (add_label_of_Nread pr_mem nr).
  exact/cfx0.
Qed.

Lemma consist_new_Nread : 
  dom_consistency (add_new_event (add_label_of_Nread pr_mem nr)).
Proof.
  rewrite /add_new_event. case: ifP=> // _; rewrite ?consist_Nread //.
  by case: ces.
Qed.

End Nread_Consist.

Definition tr_add_event es1 es2 := exists al, es2 = @add_event es1 al.

Notation "es1 '~>' es2" := (tr_add_event es1 es2) (at level 0).

Definition ltr_add_event es1 l es2 := 
  exists2 al, es2 = @add_event es1 al & l = al.

Notation "es1 '~(' l ')~>' es2" := (ltr_add_event es1 l es2) (at level 0).

Section Equivalence.

Section IsoDef.

Context (es1 es2 : exec_event_struct).

Notation dom1   := (dom   es1).
Notation lprf1  := (lprf   es1).
Notation fresh1 := (fresh_seq dom1).
Notation dom2   := (dom   es2).
Notation lprf2  := (lprf   es2).
Notation fresh2 := (fresh_seq dom2).

Definition is_morph f := 
  ((map f dom1 =i dom2) *
   (forall n, f (iter n fresh fresh1) = iter n fresh fresh2) *
   (lprf2 \o f =1 (ext f) \o lprf1))%type.

Definition is_iso f := (is_morph f * bijective f)%type.

End IsoDef.

Definition eqv : hrel exec_event_struct exec_event_struct := 
  fun es1 es2 => exists f, is_iso es1 es2 f.

Lemma eqv_refl : 1 ≦ eqv.
Proof. 
  move=> ??->. exists id; do ? split=> //; last exact/inv_bij;
  rewrite ?map_id // => ? /=; by rewrite  ext_id.
Qed.

Lemma is_iso_comp es1 es2 es3 f g: 
  is_iso es1 es2 f -> is_iso es2 es3 g ->
  is_iso es1 es3 (g \o f).
Proof.
  case=> [][][] i1 it1 l1 ?[][][] i2 it2 l2 /[dup] [[]].
  move=> ?? c1 ?.
  do ? split; last exact/bij_comp; move=> x.
  - rewrite map_comp -i2 -[x]c1 ?mem_map //; exact/bij_inj.
  - by rewrite /= it1 it2.
  by move: (l1 x) (l2 (f x))=> /=; rewrite ext_comp /= => <-.
Qed.

Lemma eqv_trans: Transitive eqv.
Proof. move=> ???[f i [g ?]]; exists (g \o f); exact/(is_iso_comp i). Qed.

Lemma eqv_symm: Symmetric eqv.
Proof.
  move=>> [f [[][] i it l /[dup] b[g c1 c2]]].
  have B: bijective g by apply/(bij_can_bij b). 
  exists g; split=> //; do ? split; move=> x /=.
  - rewrite -{1}[x]c1 mem_map -?i ?mem_map //; exact/bij_inj.
  - by apply/(bij_inj b); rewrite c2 it.
  apply/(bij_inj (bij_ext b)); move: (l (g x))=> /= <-.
  by rewrite ?(ext_can c2) c2.
Qed.

End Equivalence.

Notation "e1 ~~ e2" := (eqv e1 e2) (at level 20).
