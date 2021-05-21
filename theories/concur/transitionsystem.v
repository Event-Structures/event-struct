From RelationAlgebra Require Import lattice monoid rel kat_tac kleene.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice seq path.
From mathcomp Require Import order finmap fintype ssrnat.
From eventstruct Require Import utils eventstructure ident.
From eventstruct Require Import rewriting_system.

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
(*         add_label_of_nread == takes non-read label and predcessor and      *)
(*                    returns corresponding add_label structure               *)
(*         consist_nread == lemma that ensures consistency of event structures*)
(*                    obtained by add_label_of_Nread                          *)
(*         contain al es == checks if event that we want to add (al) is       *)
(*                    already in es                                           *)
(*         add_new_event == adding a new event to the event structrure if it  *)
(*                    is not contained there                                  *)
(*         consist_add_new_event == statement about consistance of our new    *)
(*                    structure obtained with add_new_event                   *)
(*         consist_new_nread== lemma that ensures consistency of event        *)
(*                structures obtained by add_label_of_Nread of a new event    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.LTheory.
Open Scope order_scope.
Open Scope fset_scope.

Import Label.Syntax.

(* Definition add_wr {E V : eqType} e1 e2 (lab : E -> @Lab V V) l := *)
(*   (e1 == e2) && (~~ Label.is_read l) || ((lab e1) \>> l). *)

(* Arguments add_wr /. *)

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

Notation dom  := (dom es).
Notation ffed := (fed es).
Notation flab := (lab es).
Notation ffpo := (fpo es).
Notation ffrf := (frf es).

Notation fresh_id := (fresh_seq dom).

Structure add_label := Add {
  add_lb            : label;
  add_po            : E;
  add_write         : E;

  add_pred_in_dom   : add_po \in dom;
  add_write_in_dom  : add_write \in dom;
  add_write_consist : flab add_write \>> add_lb ;
}.

Coercion of_add_label := fun
  '(Add l p w _ _ _) => mk_edescr l p w.

Lemma of_add_label_inj : injective of_add_label.
Proof.
  case=> ??? +++ [??? +++ [le pe we]].
  move: le pe we; (do ? case :_ /)=> *; congr Add; exact/eq_irrelevance.
Qed.

Variable al : add_label.

(* label of an event to add *)
Notation lb := (add_lb al).

(* predecessor of the new event (if it exists) *)
Notation pred := (add_po al).

(* if our event is `Read` then we should provide the corresponding `Write`
   event *)
Notation write := (add_write al).

Lemma pred_fresh_id : pred < fresh_id.
Proof. by move/add_pred_in_dom/(fresh_seq_lt dom_sorted): al. Qed.

Lemma write_fresh_id : write < fresh_id.
Proof. by move/add_write_in_dom/(fresh_seq_lt dom_sorted): al. Qed.

Definition contain :=
  has (fun e => (flab e == lb) && (ffrf e == write) && (ffpo e == pred)) dom.

Definition add_fed :=
  [ fsfun ffed with fresh_id |->
                    {| lab_prj := lb; fpo_prj := pred; frf_prj := write |} ].

Definition add_lab := fun e : E => lab_prj (add_fed e).
Definition add_fpo := fun e : E => fpo_prj (add_fed e).
Definition add_frf := fun e : E => frf_prj (add_fed e).

Arguments i0_fresh {_ _ _ _}.

Lemma add_fedE e :
  add_fed e = if e == fresh_id then mk_edescr lb pred write else fed es e.
Proof. by rewrite /= fsfun_withE /=; case: ifP. Qed.

Lemma add_labE e :
  add_lab e = if e == fresh_id then lb else lab es e.
Proof. by rewrite /add_lab /add_fed /= fsfun_withE /=; case: ifP. Qed.

Lemma add_fpoE e :
  add_fpo e = if e == fresh_id then pred else fpo es e.
Proof. by rewrite /add_fpo /add_fed /= fsfun_withE /=; case: ifP. Qed.

Lemma add_frfE e :
  add_frf e = if e == fresh_id then write else frf es e.
Proof. by rewrite /add_frf /add_fed /= fsfun_withE; case: ifP. Qed.

Fact add_fed_finsupp : finsupp add_fed == (seq_fset tt (fresh_id :: dom)).
Proof.
  apply/fset_eqP=> x; rewrite ?inE seq_fsetE finsupp_with.
  case: ifP; rewrite ?inE fed_dom //.
  move: pred_fresh_id=> /[swap]/eqP[?->]; by rewrite ltxx.
Qed.

Lemma add_fed0 : 
  add_fed ident0 = {| lab_prj := Init; fpo_prj := ident0; frf_prj := ident0 |}.
Proof. rewrite add_fedE lt_eqF=> //; [ exact/fed0| exact/i0_fresh_seq ]. Qed.

Fact add_fpo_dom :
  [forall e : finsupp add_fed, add_fpo (val e) \in fresh_id :: dom].
Proof.
  apply/forallP=> [[/= x]].
  rewrite (eqP add_fed_finsupp) ?inE seq_fsetE ?inE /add_fpo fsfun_withE.
  case: (x =P fresh_id) => /=; first by rewrite (add_pred_in_dom al).
  by move=> ? /fpo_dom->.
Qed.

Fact add_frf_dom :
  [forall e : finsupp add_fed, add_frf (val e) \in fresh_id :: dom].
Proof.
  apply/forallP=> [[/= x]].
  rewrite (eqP add_fed_finsupp) ?inE seq_fsetE ?inE /add_frf fsfun_withE.
  case: (x =P fresh_id)=> /=; first by rewrite (add_write_in_dom al).
  by move=> ? /frf_dom->.
Qed.

Fact add_fpo_le :
  [forall e : finsupp add_fed, add_fpo (val e) <= val e].
Proof.
  apply/forallP=> [[/=]] e. 
  rewrite (eqP add_fed_finsupp) ?inE seq_fsetE ?inE.
  rewrite add_fpoE; case: ifP=> /= [/eqP-> _|??].
  - apply/ltW/pred_fresh_id.
  exact/fpo_le. 
Qed.

Fact add_frf_le :
  [forall e : finsupp add_fed, add_frf (val e) <= val e].
Proof.
  apply/forallP=> [[/=]] e. 
  rewrite (eqP add_fed_finsupp) ?inE seq_fsetE ?inE.
  rewrite add_frfE; case: ifP=> /= [/eqP-> _|??].
  - exact/ltW/write_fresh_id.
  exact/frf_le. 
Qed.

Fact add_frf_sync :
  [forall e : finsupp add_fed, add_lab (add_frf (val e)) \>> add_lab (val e)].
Proof.
  apply/forallP=> [[/=]] e. 
  rewrite (eqP add_fed_finsupp) ?inE seq_fsetE ?inE.
  rewrite !add_labE !add_frfE.
  case: (e == fresh_id).
  - case: ifP; first by rewrite lt_eqF=> //; exact/write_fresh_id.
    move=> ??; exact/add_write_consist. 
  rewrite orFb; case: ifP=> /[swap] H. 
  - rewrite lt_eqF=> //. apply/le_lt_trans; first exact/frf_le. 
    exact/(fresh_seq_lt dom_sorted).
  move=> ?; exact/frf_sync.
Qed.

Lemma nfresh_dom0 : 
  \i0 \in fresh_id :: dom.
Proof. by rewrite ?inE dom0. Qed.

Definition add_event :=
  @Pack _ _ _
        (fresh_id :: dom)
        add_fed
        add_fed_finsupp
        (path_fresh_seq dom_sorted)
        nfresh_dom0
        add_fed0
        add_fpo_dom
        add_frf_dom
        add_fpo_le
        add_frf_le
        add_frf_sync.

Definition add_new_event := if contain then es else add_event.

Hypothesis consist : dom_consistency es.

Import Relation_Operators.

(* TODO: remove duplicate lemmas `add_fedE`, `add_labE`, etc *)

Lemma fed_add_eventE e :
  fed add_event e = if e == fresh_id then mk_edescr lb pred write else fed es e.
Proof. exact: add_fedE. Qed.

Lemma lab_add_eventE e :
  lab add_event e = if e == fresh_id then lb else lab es e.
Proof. exact: add_labE. Qed.

Lemma fpo_add_eventE e :
  fpo add_event e = if e == fresh_id then pred else fpo es e.
Proof. exact: add_fpoE. Qed.

Lemma frf_add_eventE e :
  frf add_event e = if e == fresh_id then write else frf es e.
Proof. exact: add_frfE. Qed. 

Lemma ica_add_eventE e1 e2 :
  ica add_event e1 e2 =
  if e2 == fresh_id then
    (pred == e1) || (write == e1)
  else ica es e1 e2.
Proof.
  rewrite icaE /= /fica frf_add_eventE fpo_add_eventE.
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
Proof. by rewrite /icf !fpo_add_eventE=> /negbTE->/negbTE->. Qed.

Lemma cf_add_eventE e1 e2 :
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

Lemma consist_add_event :
  ~~ (cf add_event fresh_id write) <-> dom_consistency add_event.
Proof.
  split=> [?|].
  - rewrite /dom_consistency; apply /allP=> e1.
    rewrite /frf /= fsfun_withE ?inE.
    case: ifP=> /= [/eqP-> _|/negbT N /(allP consist)] //; first exact/implyP.
    rewrite -cf_add_eventE //.
    apply/negP=> /eqP Ef.
    have /ica_fresh /eqP /(negP N) //: ica es fresh_id e1.
    by rewrite icaE /= ?inE -Ef eq_refl.
  case: (boolP (write == fresh_id))=> [/eqP<- /cf_irrelf/(_ write)->|?] //.
  move/allP/(_ fresh_id)=> /=; rewrite frf_add_eventE inE eq_refl /=.
  move/(_ erefl)/implyP; exact.
Qed.

Lemma consist_add_new_event : ~~ (cf add_event fresh_id write) -> 
dom_consistency add_new_event.
Proof. 
  rewrite /add_new_event; case: ifP=> // _. 
  exact: (proj1 consist_add_event). 
Qed.

End AddEvent.

Section NreadConsist.

Context (ces : cexec_event_struct) (pr : E) (l : label).

Notation domain := (dom ces).
Notation fresh_id := (fresh_seq domain).

Hypothesis pr_mem : pr \in domain.
Hypothesis nr     : ~~ Label.is_read l.

Fact add_nread_synch : lab ces ident0 \>> l. 
Proof. 
  rewrite lab0 /Label.synch. 
  case H: l=> //; symmetry; apply/contraPF.
  - move=> x; apply/negP; exact/nr.
  by rewrite /Label.is_read H.
Qed. 

Let add_label_nread := Add pr_mem dom0 add_nread_synch.

Lemma consist_nread :
   dom_consistency (add_event add_label_nread).
Proof. apply/consist_add_event=> //=; first (by case: ces); exact/cf0. Qed.

Lemma consist_new_nread :
  dom_consistency (add_new_event add_label_nread).
Proof.
  rewrite /add_new_event; case: ifP=> // _.
  - by case ces.
  by rewrite ?consist_nread //.
Qed.

End NreadConsist.

End TransitionSystem.

Module AddEvent.

Section Confluence.

Context {disp} (E : identType disp) (V : eqType).

Notation exec_event_struct := (@fin_exec_event_struct disp E V).
Notation cexec_event_struct := (@cexec_event_struct disp E V).

Notation label := (@Lab V V).

Implicit Types (x : Loc) (a : V) (es : exec_event_struct).

Definition tr es1 es2 := exists al, es2 = @add_event disp _ V es1 al.

Notation "es1 '~>' es2" := (tr es1 es2) (at level 0).

Definition ltr (ed : edescr E label) es1 es2 := 
  exists2 al, es2 = @add_event disp _ V es1 al & ed = al.

Notation "es1 '~(' l ')~>' es2" := (ltr l es1 es2) (at level 0).

Section Equivalence.

Section IsoDef.

Context (f : E -> E) (es1 es2 : exec_event_struct).

Definition is_morph := fed es2 \o f =1 (edescr_map f) \o fed es1.

Section Morphism.

Hypothesis morph: is_morph.

Lemma is_morph_lab e :
  lab es2 (f e) = lab es1 e.
Proof.
  move/(congr1 (@lab_prj _ _)): (morph e).
  by rewrite /lab /=; case: (fed es1 e).
Qed.

Lemma is_morph_po e :
  fpo es2 (f e) = f (fpo es1 e).
Proof.
  move/(congr1 (@fpo_prj _ _)): (morph e).
  by rewrite fpo_prj_edescr_map.
Qed.

Lemma is_morph_rf e :
  frf es2 (f e) = f (frf es1 e).
Proof.
  move/(congr1 (@frf_prj _ _)): (morph e).
  by rewrite frf_prj_edescr_map.
Qed.

Lemma is_morph_ica e1 e2 : 
  ica es1 e1 e2 -> ica es2 (f e1) (f e2).
Proof.
  rewrite ?icaE /fica /= ?inE is_morph_po is_morph_rf=> /orP[]/eqP->;
  by rewrite eq_refl.
Qed.

Lemma is_morph_ca e1 e2 : 
  ca es1 e1 e2 -> ca es2 (f e1) (f e2).
Proof.
  move/closure_n1P; elim=> [|??/is_morph_ica I ?]; first exact/ca_refl.
  move/closure_n1P=> ?; apply/closure_n1P.
  by apply/Relation_Operators.rtn1_trans; first by exact/I.
Qed.

End Morphism.


Definition is_iso := is_morph /\ bijective f.

Section IsoMorphism.

Hypothesis iso : is_iso.

Lemma iso_dom : map f (dom es1) =i dom es2.
Proof.
  case: iso=> l /[dup] B [g /[dup] c1 /can_inj I c2 x].
  rewrite -[x]c2 (mem_map I) !fed_dom_mem !mem_finsupp. 
  move: (l (g x))=> /= ->.
  rewrite -[_ _ (f _) _]/(edescr_map f (mk_edescr _ _ _)).
  by rewrite (bij_eq (@edescr_map_bij label E E _ B)).
Qed.

Lemma f_icf e1 e2 :
  icf es1 e1 e2 -> icf es2 (f e1) (f e2).
Proof.
  case: iso=> ??.
  by rewrite/icf ?lt_neqAle ?fpo_le ?andbT ?is_morph_po ?(bij_eq (f := f)).
Qed.

Lemma f_cf e1 e2 :
  es1 |- e1 # e2 -> es2 |- (f e1) # (f e2).
Proof.
  case: iso=> ?? /cfP [x [y H]]; apply/cfP; exists (f x), (f y).
  by rewrite ?is_morph_ca ?f_icf ?H.
Qed.

End IsoMorphism.

End IsoDef.

Lemma is_iso_can es1 es2 f g :
  is_iso f es1 es2 -> cancel f g -> cancel g f -> 
  is_iso g es2 es1.
Proof.
  move=> [l b c1 c2].
  have B: bijective g by apply/(bij_can_bij b). 
  split=> //; do ? split; try move=> x /=.
  apply/(bij_inj (@edescr_map_bij label _ _ _ b)). 
  move: (l (g x))=> /= <-.
  by rewrite ?(edescr_map_can c2) c2.
Qed.

Lemma isoE f e1 e2 es1 es2: is_iso f es1 es2 -> 
  ( 
    (lab es2 (f e1) = lab es1 e1) *
    ((fpo es2 (f e1) = f (fpo es1 e1)) *
    (frf es2 (f e1) = f (frf es1 e1))) *
    ((ca es2 (f e1) (f e2) = ca es1 e1 e2) *
    (cf es2 (f e1) (f e2) = cf es1 e1 e2))
  )%type.
Proof.
  move=> /[dup] If [M []? /[dup] c /(is_iso_can If) /[apply] Ig].
  do ? split; rewrite ?(is_morph_po M) ?(is_morph_lab M) ?(is_morph_rf M) //.
  - apply/(sameP idP)/(equivP idP).
    split=> [/(is_morph_ca M)//|/(is_morph_ca Ig.1)]; by rewrite ?c.
  apply/(sameP idP)/(equivP idP).
  split=> [/(f_cf If)//|/(f_cf Ig)]; by rewrite ?c.
Qed.

Lemma eq_is_iso f g es1 es2 : f =1 g ->
  is_iso f es1 es2 <-> is_iso g es1 es2.
Proof.
  move=> /[dup] /fsym H1 H2; rewrite /is_iso /is_morph.
  have->: bijective f <-> bijective g.
  - by split=> [/eq_bij/(_ _ H2) |/eq_bij/(_ _ H1)]. 
  apply/(and_iff_compat_r (bijective g)).
  split=> H x; move: (H x)=> /=; rewrite (H1, H2)=>->;
    by under edescr_map_eqfun=> ? do rewrite (H1, H2) over //.
Qed.

Definition eqv := exlab is_iso.

Lemma eqv_refl : 1 ≦ eqv.
Proof. 
  move=> ??->. exists id; do ? split=> //; last exact/inv_bij;
  rewrite ?map_id // => ? /=; by rewrite edescr_map_id.
Qed.

Lemma is_iso_comp es1 es2 es3 f g :
  is_iso f es1 es2 -> is_iso g es2 es3 ->
  is_iso (g \o f) es1 es3 .
Proof.
  case=> [] l1 ?[] l2 /[dup] [[?? c1 ?]] .
  (do ? split)=>[x|]; last exact/bij_comp. 
  by move: (l1 x) (l2 (f x))=> /=; rewrite edescr_map_comp /= => <-.
Qed.

Lemma eqv_trans : Transitive eqv.
Proof. move=> ???[f i [g ?]]; exists (g \o f); exact/(is_iso_comp i). Qed.

Lemma eqv_symm : Symmetric eqv.
Proof. move=>> [? /[dup] I [_ [f *]]]; exists f; exact/(is_iso_can I).  Qed.

End Equivalence.

Notation "e1 ~~ e2" := (eqv e1 e2) (at level 20).

Notation fresh_id1  es := (fresh_seq (dom es)).
Notation fresh_id2 es := (fresh_seq (fresh_seq (dom es) :: dom es)).

Lemma is_iso_swap es1 es2 f e1 e2 :
  e1 \notin dom es1 ->
  e2 \notin dom es1 ->
  is_iso f es1 es2 -> 
  is_iso (swap f e1 e2) es1 es2.
Proof.
  move=> N1 N2 /[dup] I [ l /[dup] /bij_inj ? b].
  case: (e1 =P e2)=> /= [->|/eqP/negbTE e12].
  - by under eq_is_iso=> ? do rewrite swapxx over //.
  (do ? split)=> [x/=|]; last exact/bij_swap.
  have H: forall e es, e \notin dom es -> fed es e = mk_edescr Eps e e.
  - by move=> ?? D; rewrite fsfun_dflt // fed_dom D.
  rewrite /swap; case: ifP=> [/eqP->|].
  - rewrite ?H /= ?eq_refl // -?(iso_dom I) mem_map //.
  case: ifP=> [/eqP-> N|F1 F2].
  rewrite ?H //= ?N ?eq_refl // -?(iso_dom I) mem_map //.
  case: (boolP (x \in dom es1))=> [/[dup]/fpo_dom I1 /frf_dom I2|?].
  - apply/eqP; rewrite edescr_eq.
    rewrite lab_prj_edescr_map fpo_prj_edescr_map frf_prj_edescr_map.
    rewrite ?(negbTE (memPn _ _ I1)) ?(negbTE (memPn _ _ I2)) //.
    move: (l x)=> /=->.
    rewrite lab_prj_edescr_map fpo_prj_edescr_map frf_prj_edescr_map. 
    by rewrite !eq_refl.
  by rewrite ?H //= ?F1 ?F2 //  -?(iso_dom I) mem_map.
Qed.

Arguments Add {_ _ _ _} _ _ _.

Lemma comm_eqv_tr :
  diamond_commute eqv tr.
Proof.
  move=> es es3 ? /[swap][][[al ap aw apd awd awc]]->.
  case=> f /[dup][[_ [g? c]]] I.
  have NI: g (fresh_id1 es3) \notin dom es.
  - rewrite -(mem_map (bij_inj (proj2 I))) c (iso_dom I) fresh_seq_notin //.
    exact/dom_sorted.
  move/(is_iso_swap (fresh_seq_notin dom_sorted) NI): I.
  set h := (swap f (fresh_id1 es) (g (fresh_id1 es3))).
  move=> /[dup] I [ l /[dup] /bij_inj ? b].
  have H: forall e, e \in dom es -> h e \in dom es3=> [e|].
  by rewrite -(iso_dom I) mem_map.
  have [: a1 a2 a3] @s4: add_label es3 := Add al (h ap) (h aw) a1 a2 a3.
  1,2: by apply/H; rewrite (apd, awd).
  - move: awc; move: (l aw)=> /=; rewrite /lab.
    by case L1: (fed _ aw)=> /=; case L2: (fed es3 (f aw))=> -> /=. 
  exists (add_event s4); [by exists s4 | exists h].
  (do ? split)=> // x /=.
  rewrite ?fed_add_eventE /= -[fresh_id1 _]c -(swap1 f (fresh_id1 es)).
  rewrite -/h (bij_eq b); case: ifP=> // ?; exact/l. 
Qed.

Lemma swap_dom es e : e \in dom es -> 
  swap id (fresh_id1 es) (fresh_id2 es) e = e.
Proof.
  move=> /(fresh_seq_lt (dom_sorted)) /[dup]. 
  move/lt_trans/(_ (fresh_lt _))/lt_eqF/negbT=> ? /lt_eqF/negbT ?.
  by rewrite -swap_not_eq.
Qed.

Lemma add_add (es : exec_event_struct) 
  (al1 al2 : add_label es) : 
  exists al : add_label (add_event al1), 
  al = al2 :> edescr E label.
Proof.
  case: al2=> l p w ap aw ?.
  have [:a1 a2 a3] @al : add_label (add_event al1) := 
    Add l p w a1 a2 a3; try by rewrite ?inE (ap, aw) orbT.
  - by rewrite /= lab_add_eventE (lt_eqF (fresh_seq_lt dom_sorted aw)).
  by exists al; rewrite ?(swap_dom (lexx _)).
Qed.

Lemma swap_add es 
  (al1 al2 : add_label es)
  (al3 : add_label (add_event al1))
  (al4 : add_label (add_event al2)) :
  al1 = al4 :> edescr E label ->
  al2 = al3 :> edescr E label ->
  is_iso (swap id (fresh_id1 es) (fresh_id2 es))
    (add_event al3) (add_event al4) .
Proof.
  case: al1 al3 al2 al4=> ??????[/=???+++] [??????[/=???+++ E1 E2]].
  case: E1 E2; do 3? case:_/; case; (do 3? case:_/)=>*.
  do ? split; last exact/bij_swap/inv_bij.
  move=> x /=; rewrite /comp !fed_add_eventE /=.
  have: fresh_id1 es <> fresh_id2 es by move/(@fresh_iter _ _ 1 2).
  move/eqP/negbTE=>F; case: (x =P fresh_id1 es)=> [->|/eqP/[dup] ? /negbTE N1].
  - rewrite swap1 eq_refl F /= !swap_dom //.
  rewrite ?inv_eq ?swap1 ?swap2 ?N1; try exact/swap_inv.
  case: ifP=> //=; first by rewrite !swap_dom=> //.
  move/negbT=> ?; rewrite -swap_not_eq //.
  case: (boolP (x \in dom es))=> [|I]. 
  - case L: (fed _ x)=> [l p r] I /=; apply/congr2; rewrite swap_dom //.
    - by rewrite -[p]/(fpo_prj (mk_edescr l p r)) -L fpo_dom.
    by rewrite -[r]/(frf_prj (mk_edescr l p r)) -L frf_dom.
  by rewrite fsfun_dflt /= -?swap_not_eq // fed_dom I.
Qed.

Lemma comm_ltr l1 l2 :
  eqv_diamond_commute (ltr l1) (ltr l2) eqv.
Proof.
  move=> es ?? [al1 -> /[swap][[al2->]]].
  case: (add_add al1 al2)=> al3 /[dup]? <-->.
  case: (add_add al2 al1)=> al4 /[dup]? <-->.
  exists (add_event al3), (add_event al4).
  split; [by exists al3| by exists al4|].
  exists (swap id (fresh_id1 es) (fresh_id2 es)); exact/swap_add.
Qed.

Lemma exlab_tr : tr ≡ exlab ltr.
Proof. by move=> ??; split=> [[l ->]|[?[l ->]]]; do ? exists l. Qed.

Arguments isoE {_ _ _ _ _}.

Lemma dom_consist_eqv es1 es2 :
  es1 ~~ es2 -> dom_consistency es1 ->
  dom_consistency es2.
Proof.
  rewrite /dom_consistency=> [[f /[dup] If]] [L ? /allP H]; apply/allP.
  move=> x; rewrite -(iso_dom If)=> /mapP[y /H ?->].
  move/(congr1 (@frf_prj _ _)): (L y)=> /=; rewrite -frfE=>->.
  by rewrite frf_prj_edescr_map bij_eq // (isoE If).
Qed.

Lemma dom_consist_add l1 l2 
  (es1 es2 es3 es4 : exec_event_struct) :
  dom_consistency es1 ->
  es1 ~(l1)~> es2 -> dom_consistency es2 -> 
  es1 ~(l2)~> es3 -> dom_consistency es3 ->
  es2 ~(l2)~> es4 -> dom_consistency es4.
Proof.
  move=> ?; case=> [[la1 p1 w1 ap1 aw1 ac1 ->]].
  set al1 := Add _ _ _ ap1 aw1 ac1=> e2; move=> C'.
  case=> [[l p w ap aw ac]]+->; set al2 := Add _ _ _ ap aw ac=> -> C.
  case=> [[l' p' ap' +++-> [le pe we]]].
  move: le pe we; (do ? case: _/).
  move=> ap2 aw2 ac2; set al2' := Add _ _ _ ap2 aw2 ac2.
  apply/consist_add_event=> //=.
  set f := swap id (fresh_id1 es1) (fresh_id2 es1).
  have P : f p1 = p1 by rewrite /f (swap_dom ap1).
  have W : f w1 = w1 by rewrite /f (swap_dom aw1).
  have [: a1 a2 a3] @al3 : add_label (add_event al2) 
    := Add la1 (f p1) (f w1) a1 a2 a3=> /=.
  1,2: rewrite ?inE (P, W) (ap1, aw1); lattice.
  - by rewrite W  lab_add_eventE (lt_eqF (write_fresh_id al1)).
  have E1: al1 = al3 :> edescr _ _ by rewrite /= W P.
  have E2: al2 = al2' :> edescr _ _ by [].
  rewrite -(isoE (swap_add E1 E2)) swap2 (swap_dom aw) //.
  rewrite -cf_add_eventE; first exact/consist_add_event.
  - by apply/eqP=> /(@fresh_iter _ _ 1 2).
  by rewrite (lt_eqF (write_fresh_id al2')).
Qed.

End Confluence.

End AddEvent.
