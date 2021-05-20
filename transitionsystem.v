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
  add_write_consist : add_wr add_write \i0 flab add_lb;
}.

Coercion of_add_label := fun
  '(Add l p w _ _ _) => Lprf l p w.

Lemma of_add_label_inj: injective of_add_label.
Proof.
  case=> ??? +++ [??? +++ [le pe we]].
  move: le pe we; (do ? case :_ /)=> *; congr Add; exact/eq_irrelevance.
Qed.

Fact add_write_consist_of_fresh l : ~~ Label.is_read l ->
  add_wr \i0 \i0 flab l.
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

Arguments i0_fresh {_ _ _ _}.

Fact add_lprf_finsupp : finsupp add_lprf == (seq_fset tt (fresh_id :: dom) `\ \i0).
Proof.
  apply/fset_eqP=> x; rewrite ?inE seq_fsetE finsupp_with.
  case: ifP; rewrite ?inE lprf_dom // mem_filter.
  - move: pred_fresh_id=> /[swap]/eqP[?->]; by rewrite ltxx.
  case: (x =P fresh_id)=> //=-> ?; rewrite andbT eq_sym.
  exact/esym/negbT/lt_eqF/i0_fresh.
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
    (w == \i0) && ~~ Label.is_read (add_lab r) || (add_lab w) \>> (add_lab r)].
Proof.
  apply/forallP=> [[r /=]]; rewrite (@seq_fsetE tt).
  rewrite /add_frf /add_lab /add_lprf !fsfun_withE /= ?inE.
  case: ifP=> /= [/eqP|?/[dup]/frf_cond /[swap]].
  - case: ifP=> [/eqP|*]; last exact/add_write_consist.
    - move/lt_eqF/eqP: write_fresh_id; exact.
  by move/(fresh_seq_lt dom_sorted)/(le_lt_trans (frf_le _ _))/lt_eqF->.
Qed.

Lemma Nfresh_dom0: 
  \i0 \in fresh_id :: dom.
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

Definition ltr_add_event (l : lab_pred_rfrom E V) es1 es2 := 
  exists2 al, es2 = @add_event es1 al & l = al.

Notation "es1 '~(' l ')~>' es2" := (ltr_add_event l es2 es2) (at level 0).

Section Equivalence.

Section IsoDef.

Context (f : E -> E) (es1 es2 : exec_event_struct).

Definition is_morph := 
  f \i0  = \i0 /\ lprf es2 \o f =1 (ext f) \o lprf es1.

Definition is_iso := is_morph /\ bijective f.

Lemma iso_dom: is_iso ->
  map f (dom es1) =i dom es2.
Proof.
  move=> [[i l] /[dup] B [g /[dup] c1 /can_inj I c2 x]].
  rewrite -[x]c2 (mem_map I) ?lprf_finsupp -(bij_eq B) c2 i.
  case: (boolP (x == \i0))=> //=. rewrite -{-2}[x]c2 -i (bij_eq B).
  set y := g x; rewrite ?mem_finsupp; move: (l y)=> /=->.
  rewrite -[Lprf ThreadEnd (f y) (f y)]/(ext f (Lprf ThreadEnd y y)).
  by rewrite (bij_eq (bij_ext _ B)).
Qed.

Lemma iso0: is_iso -> f \i0 = \i0.
Proof. by do 2? case. Qed.

End IsoDef.

Definition eqv := exlab is_iso.

Lemma eqv_refl : 1 ≦ eqv.
Proof. 
  move=> ??->. exists id; do ? split=> //; last exact/inv_bij;
  rewrite ?map_id // => ? /=; by rewrite  ext_id.
Qed.

Lemma is_iso_comp es1 es2 es3 f g: 
  is_iso f es1 es2 -> is_iso g es2 es3 ->
  is_iso (g \o f) es1 es3 .
Proof.
  case=> [][] i1 l1 ?[][] i2 l2 /[dup] [[?? c1 ?]] .
  (do ? split)=>[|x|]; last exact/bij_comp; first by  rewrite /= i1 i2. 
  by move: (l1 x) (l2 (f x))=> /=; rewrite ext_comp /= => <-.
Qed.

Lemma eqv_trans: Transitive eqv.
Proof. move=> ???[f i [g ?]]; exists (g \o f); exact/(is_iso_comp i). Qed.

Lemma is_iso_can es1 es2 f g: 
  is_iso f es1 es2 -> cancel f g -> cancel g f -> 
  is_iso g es2 es1.
Proof.
  move=> [[] i l b c1 c2].
  have B: bijective g by apply/(bij_can_bij b). 
  split=> //; do ? split; try move=> x /=.
  - by rewrite -{1}i c1.
  apply/(bij_inj (bij_ext _ b)); move: (l (g x))=> /= <-.
  by rewrite ?(ext_can c2) c2.
Qed.

Lemma eqv_symm: Symmetric eqv.
Proof. move=>> [? /[dup] I [_ [f *]]]; exists f; exact/(is_iso_can I).  Qed.

End Equivalence.

Notation "e1 ~~ e2" := (eqv e1 e2) (at level 20).

Section Confluence.

Notation fresh_id  es := (fresh_seq (dom es)).
Notation fresh_id2 es := (fresh_seq (fresh_seq (dom es) :: dom es)).

Lemma is_iso_swap es1 es2 f g: 
  cancel f g -> cancel g f ->
  is_iso f es1 es2 -> 
  is_iso (swap f (fresh_id es1) (g (fresh_id es2))) es1 es2.
Proof.
  move=> c1 c2 I; move: (is_iso_can I c1 c2) (I).
  move=> Ig [[i l /[dup] /bij_inj ? b]].
  (do ? split)=> [|x/=|]; last exact/bij_swap.
  rewrite -swap_not_eq // -[\i0]c1 ?bij_eq ?(c1, i) ?(lt_eqF (i0_fresh_seq _)) //.
  - exact/(bij_can_bij b).
  rewrite /swap; case: ifP=> [/eqP->|].
  - rewrite c2 ?lprf_Ndom /= ?eq_refl //; exact/(fresh_seq_notin dom_sorted).
  case: ifP=> [/eqP->|].
  - rewrite ?lprf_Ndom /= ?c2 ?eq_refl.
    - case: ifP=> [/eqP<-|//]; first by rewrite c2.
      - rewrite -(iso_dom Ig) mem_map ?(fresh_seq_notin dom_sorted) //.
        exact/(can_inj c2).
      by rewrite -(iso_dom I) mem_map ?(fresh_seq_notin dom_sorted).
  move=> N1 N2. apply/eqP. rewrite lab_pred_rfromE. 
  apply/andP; split; [|apply/andP; split].
  - by move: (l x)=> /= ->; rewrite /= !lab_prj_ext. 
  - move/(congr1 (@fpred_prj _ _ _)): (l x)=> /=.
    rewrite /= !fpred_prj_ext. 
    case: ifP=> [/eqP/fpred_fresh N|].
    - by rewrite N eq_refl in N2.
    case: ifP=> [|??->] // /eqP/(congr1 f)=> ++ N; rewrite -N c2.
    move/fpred_fresh/(congr1 g); rewrite c1=> {N}N.
    by rewrite N eq_refl in N1.
  move/(congr1 (@frf_prj _ _ _)): (l x)=> /=.
  rewrite /= !frf_prj_ext. 
  case: ifP=> [/eqP/frf_fresh N|].
  - by rewrite N eq_refl in N2.
  case: ifP=> [|??->] // /eqP /(congr1 f) ++ N; rewrite -N c2.
  move/frf_fresh/(congr1 g); rewrite c1=> {N}N.
  by rewrite N eq_refl in N1.
Qed.

Lemma comm_eqv_tr :
  diamond_commute eqv tr_add_event.
Proof.
  move=> es es3 ? /[swap][][[al ap aw apd awd awc]]->.
  case=> f /[dup][/is_iso_swap C [_[g {C}/C C /[dup] c /C]]].
  set h := (swap f (fresh_id es) (g (fresh_id es3))).
  move=> /[dup] I [[] i l /[dup] /bij_inj ? b].
  have H: forall e, e \in dom es -> h e \in dom es3=> [e|].
  by rewrite -(iso_dom I) mem_map.
  have [: a1 a2 a3] @s4: add_label es3 := @Add _ al (h ap) (h aw) a1 a2 a3.
  1,2: by apply/H; rewrite (apd, awd).
  - move: awc; rewrite /add_wr -{2}(iso0 I) bij_eq // /lab; move: (l aw)=> /=.
    case L: (lprf _ aw)=> /=; case L': (lprf es3 (f aw))=> /=; by move=>->.
  exists (add_event s4); [by exists s4 | exists h].
  (do ? split)=> // x /=.
  rewrite ?lprf_add_eventE /= -[fresh_id _]c -(swap1 f (fresh_id es)).
  rewrite -/h (bij_eq b); case: ifP=> // ?; exact/l. 
Qed.

Lemma swap_dom es d e: e <= d -> d \in dom es -> 
  swap id (fresh_id es) (fresh_id2 es) e = e.
Proof.
  move/le_lt_trans=> L /(fresh_seq_lt (dom_sorted)) /L /[dup]. 
  move/lt_trans/(_ (fresh_lt _))/lt_eqF/negbT=> ? /lt_eqF/negbT ?.
  by rewrite -swap_not_eq.
Qed.

Lemma add_add (es : exec_event_struct) 
  (al1 al2 : add_label es) : 
  exists al : add_label (add_event al1), 
  al = al2 :> lab_pred_rfrom E V.
Proof.
  case: al2=> l p w ap aw ?.
  have [:a1 a2 a3] @al : add_label (add_event al1) := 
    @Add _ l p w a1 a2 a3; try by rewrite ?inE (ap, aw) orbT.
  - by rewrite /= lab_add_eventE (lt_eqF (fresh_seq_lt dom_sorted aw)).
  by exists al; rewrite ?(swap_dom (lexx _)).
Qed.

Lemma swap_add es 
  (al1 al2 : add_label es)
  (al3 : add_label (add_event al1))
  (al4 : add_label (add_event al2)) : 
  al1 = al4 :> lab_pred_rfrom E V ->
  al2 = al3 :> lab_pred_rfrom E V ->
  is_iso (swap id (fresh_id es) (fresh_id2 es))
    (add_event al3) (add_event al4) .
Proof.
  case: al1 al3 al2 al4=> ??????[/=???+++] [??????[/=???+++ E1 E2]].
  case: E1 E2; do 3? case:_/; case; (do 3? case:_/)=>*.
  do ? split; last exact/bij_swap/inv_bij.
  - by rewrite -swap_not_eq // lt_eqF // i0_fresh_seq.
  move=> x /=; rewrite /comp ?lprf_add_eventE /=.
  have: fresh_id es <> fresh_id2 es by move/(@fresh_iter _ _ 1 2).
  move/eqP/negbTE=> F; case: (x =P fresh_id es)=> [->|/eqP/[dup] ? /negbTE N1].
  - rewrite swap1 eq_refl F /= ?(swap_dom (lexx _)) //.
  rewrite ?inv_eq ?swap1 ?swap2 ?N1; try exact/swap_inv.
  case: ifP=> //=; first rewrite ?(swap_dom (lexx _)) //.
  move/negbT=> ?; rewrite -swap_not_eq //.
  case: (boolP (x \in dom es))=> [|I]. 
  - case L: (lprf _ x)=> [l p r] I /=; apply/congr2; rewrite (swap_dom _ I) //.
    - by rewrite -[p]/(fpred_prj (Lprf l p r)) -L fpred_le.
    by rewrite -[r]/(frf_prj (Lprf l p r)) -L frf_le.
  by rewrite fsfun_dflt /= -?swap_not_eq // lprf_dom mem_filter negb_and I.
Qed.

Lemma comm_ltr l1 l2: 
  eqv_diamond_commute (ltr_add_event l1) (ltr_add_event l2) eqv.
Proof.
  move=> es ?? [al1 -> /[swap][[al2->]]].
  case: (add_add al1 al2)=> al3 /[dup]? <-->.
  case: (add_add al2 al1)=> al4 /[dup]? <-->.
  exists (add_event al3), (add_event al4).
  split; [by exists al3| by exists al4|].
  exists (swap id (fresh_id es) (fresh_id2 es)); exact/swap_add.
Qed.

Lemma exlab_tr: tr_add_event ≡ exlab ltr_add_event.
Proof. by move=> ??; split=> [[l ->]|[?[l ->]]]; do ? exists l. Qed.

End Confluence.

End TransitionSystem.
