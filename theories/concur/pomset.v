From Coq Require Import Relations.
From RelationAlgebra Require Import lattice monoid rel boolean.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq tuple.
From mathcomp Require Import eqtype choice order generic_quotient.
From mathcomp Require Import fintype finfun finset fingraph finmap.
From mathcomp.tarjan Require Import extra acyclic Kosaraju acyclic_tsorted. 
From eventstruct Require Import utils rel relalg inhtype ident lposet.

(******************************************************************************)
(* This file contains theory of finitely supported labelled posets,           *)
(* pomsets represented as their quotients, and pomset languages, i.e.         *)
(* propositional predicates over pomsets.                                     *)
(* Finitely supported lposet is encoded as a finitely supported function      *)
(* from event to its label and a sequence of its immediate predecessors.      *)
(*                                                                            *)
(*      lfspreposet E L bot == finitelly supported labelled pre-poset over    *)
(*                             type of events E and type of labels L.         *)
(*                          := { fsfun E -> (L * seq E) of e => (bot, [::]) } *)
(*                             s.t. given an event e in support,              *)
(*                             f(e) == (l, es), where l is label of e and     *)
(*                             es are immediate predecessors of e.            *)
(*                             Outside of the support, f(e) == (bot, [::]),   *)
(*                             where bot is some default label.               *) 
(*         lfsposet E L bot == finitelly supported labelled poset.            *)
(*                             It is a preposet satisfying additionally that: *)
(*                               (1) all predecessors of each event belong    *)
(*                                   to the support of poset;                 *)
(*                               (2) causality relation is partial order.     *)
(*                             lfsposet is a subType of lfspreposet and thus  *)
(*                             coerces to it. Moreover, both types have       *)
(*                             instances of eqType and choiceType.            *)
(*           pomset E L bot == pomset - a class of isomorphic finitely        *)
(*                             supported lposets, defined as a quotient type  *)
(*                             over finitely supported lposets by             *)
(*                             isomorphism relation.                          *)
(*    fs_(lab|ica|ca|sca) p == labelling function, immediate causality,       *)
(*                             causality and strict causality relations of    *)
(*                             the preposet/poset/pomset p.                   *) 
(*   fin_(lab|ica|ca|sca) p == same functions/relations but defined on        *)
(*                             the finite type of support of the p.           *)
(*                                                                            *)  
(* Given a lfsposet (or pomset) one can obtain the induced lPoset structure   *)  
(* using the following notations.                                             *)  
(*             [Event of p] == lPoset.eventType structure induced by p.       *)
(*                             The type of the events are the same as of p.   *) 
(*          [FinEvent of p] == lFinPoset.eventType structure induced by p.    *)
(*                             The type of the events are of the finite       *)
(*                             support of p.                                  *)
(*                                                                            *)  
(******************************************************************************)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.
Import Order.LTheory.

Local Open Scope order_scope.
Local Open Scope fset_scope.
Local Open Scope quotient_scope.
Local Open Scope ra_terms.
Local Open Scope lposet_scope.

Declare Scope pomset_scope.
Delimit Scope pomset_scope with pomset.

Local Open Scope pomset_scope.

(* TODO: move to utils? *)
Definition eqb_cast (x y : bool) :
  (x = y) -> x -> y := fun e => let: erefl := e in id.


Notation lfspreposet E L bot := 
  ({ fsfun E -> (L * {fset E}) of e => (bot, fset0) }).

Module lFsPrePoset.

Module Export Def.
Section Def. 
Context (E : identType) (L : eqType).
Variable (bot : L).
Implicit Types (p : lfspreposet E L bot).

Definition fs_lab p : E -> L := 
  fun e => (p e).1. 

Definition fin_lab p : finsupp p -> L := 
  fun e => fs_lab p (val e).

Definition fs_rcov p : E -> {fset E} := 
  fun e => (p e).2. 

Definition fs_ica p : rel E := 
  [rel x y | grel (fs_rcov p) y x]. 

Definition fin_ica p : rel (finsupp p) := 
  sub_rel_down (fs_ica p).

Definition fin_ca p : rel (finsupp p) := 
  connect (@fin_ica p).

Definition fin_sca p : rel (finsupp p) := 
  fun e1 e2 => (e2 != e1) && (@fin_ca p e1 e2).

Definition fs_ca p : rel E := 
  (sub_rel_lift (@fin_ca p) : {dhrel E & E})^?.

Definition fs_sca p : rel E := 
  fun e1 e2 => (e2 != e1) && (fs_ca p e1 e2).

Definition lab_defined p := 
  [forall e : finsupp p, fs_lab p (val e) != bot].

Definition supp_closed p := 
  [forall e : finsupp p, all (fun e' => e' \in finsupp p) (fs_rcov p (val e))].

Definition lfsp_tseq p : seq E := 
  map val (tseq (rgraph (@fin_ica p))).

Definition lfsp_idx p : E -> nat := 
  fun e => index e (lfsp_tseq p). 

Definition lfsp_event p e0 : nat -> E := 
  fun n => nth e0 (lfsp_tseq p) n.

End Def.

Arguments fs_ica {E L bot} p.
Arguments fs_sca {E L bot} p.
Arguments  fs_ca {E L bot} p.

Arguments fin_ica {E L bot} p.
Arguments fin_sca {E L bot} p.
Arguments  fin_ca {E L bot} p.

End Def.

Section Build.
Context {E : identType} {L : eqType}.
Variable (bot : L). 
Context {P : pred E} {fE : subFinType P}.
Variables (lab : fE -> L) (ica : rel fE).

Implicit Types (p : lfspreposet E L bot).

Definition build : lfspreposet E L bot := 
  let rcov e := [fsetval e' in rgraph [rel x y | ica y x] e] in
  [fsfun e in [fset (val e) | e : fE] => 
    if (insub e) is Some e then 
      (lab e, rcov e) 
    else 
    (bot, fset0)
  | (bot, fset0)
  ].

Hypothesis (labD : forall e, lab e != bot).

Lemma build_in_finsupp e : 
  e \in finsupp build = P e.
Proof. 
  rewrite /build finsupp_fset !in_fset !inE in_fsetval /=.
  case: insubP=> [|/negPf] // e' -> ?.
  by rewrite xpair_eqE negb_and labD=> /=.
Qed.

Lemma build_finsupp : 
  finsupp build = [fsetval e in fE].
Proof. 
  apply/fsetP=> e. 
  rewrite build_in_finsupp in_fsetval. 
  by case: insubP=> [|/negPf].
Qed.

Definition event_of : finsupp build -> fE := 
  fun e => Sub (val e) (eqb_cast (build_in_finsupp (val e)) (valP e)). 

Definition of_event : fE -> finsupp build := 
  fun e => Sub (val e) (eqb_cast (esym (build_in_finsupp (val e))) (valP e)). 

Lemma build_lab : 
  fs_lab build =1 sub_lift (fun=> bot) lab.
Proof. 
  rewrite /fs_lab=> x /=. 
  rewrite fsfun_fun in_fsetval.
  case: insubP=> [x' Px valx|/negP ?] /=; last first. 
  - by rewrite sub_liftF.
  rewrite sub_liftT /=. 
  have ->: x' = Sub x Px=> //.
  apply/val_inj=> //=.
  by rewrite valx SubK. 
Qed.

Lemma build_ica : 
  fs_ica build =2 sub_rel_lift ica.
Proof. 
  rewrite /build /fs_ica /fs_rcov=> x y /=. 
  rewrite fsfun_fun in_fsetval.
  case: insubP=> [y' Py valy|/negP ?] /=; last first.
  (* TODO: make lemma for `sub_rel_lift r x y` where ~ p x \/ ~ p y *)
  - by rewrite inE /sub_rel_lift /=; case: insubP=> //; case: insubP. 
  rewrite in_fsetval_seq. 
  case: insubP=> [x' Px valx|/negP ?] /=; last first.
  - by rewrite /sub_rel_lift /=; case: insubP=> //; case: insubP. 
  rewrite -valx -valy sub_rel_lift_val; exact/rgraphK.
Qed.

Lemma build_fin_ca : 
  fin_ca build =2 connect [rel x y | ica (event_of x) (event_of y)].
Proof. admit. Admitted.
(*   rewrite /build /fs_ica /fs_rcov=> x y /=.  *)
(*   rewrite fsfun_fun in_fsetval. *)
(*   case: insubP=> [y' Py valy|/negP ?] /=; last first. *)
(*   (* TODO: make lemma for `sub_rel_lift r x y` where ~ p x \/ ~ p y *) *)
(*   - by rewrite inE /sub_rel_lift /=; case: insubP=> //; case: insubP.  *)
(*   rewrite in_fsetval_seq.  *)
(*   case: insubP=> [x' Px valx|/negP ?] /=; last first. *)
(*   - by rewrite /sub_rel_lift /=; case: insubP=> //; case: insubP.  *)
(*   rewrite -valx -valy sub_rel_lift_val; exact/rgraphK. *)
(* Qed. *)


End Build.

Module Export Theory.
Section Theory.
Context (E : identType) (L : eqType).
Variable (bot : L).
Implicit Types (p : lfspreposet E L bot).

Lemma lab_definedP p : 
  reflect (forall e, e \in finsupp p -> fs_lab p e != bot) (lab_defined p).
Proof. 
  rewrite /lab_defined /fs_lab. 
  apply/equivP; first exact/forallP.
  split=> H e /=.
  - case: finsuppP=> //= inP _.
    by rewrite (H (Sub e inP)).
  by rewrite (H (val e) (valP e)).
Qed.

Lemma supp_closedP p : 
  reflect (forall e1 e2, fs_ica p e1 e2 -> 
            (e1 \in finsupp p) && (e2 \in finsupp p))
          (supp_closed p).
Proof. 
  rewrite /supp_closed /fs_ica /fs_rcov. 
  apply/(equivP forallP); split=> /=; last first.
  - move=> ica_supp; case=> e2 in_supp /=. 
    by apply/allP=> e1 /ica_supp /andP[].
  move=> all_supp e1 e2 /=.
  case: (in_fsetP (finsupp p) e2)=> [e2'|].
  - by move: (all_supp e2')=> /allP /[swap] /= <- /[apply] ->.
  by move=> /fsfun_dflt -> //.
Qed.

Lemma fin_ica_mono p :
  { mono val : e1 e2 / fin_ica p e1 e2 >-> fs_ica p e1 e2 }.
Proof. by move=> e1 e2; rewrite /fin_ica /sub_rel_down /=. Qed.

Lemma fin_ca_mono p : 
  { mono val : e1 e2 / fin_ca p e1 e2 >-> fs_ica p e1 e2 }.  
Proof. 
  admit. 
Admitted.

Lemma lfsp_tseq_size p : 
  size (lfsp_tseq p) = #|`finsupp p|. 
Proof. by rewrite /lfsp_tseq size_map size_tseq cardfE. Qed.

Lemma lfsp_tseq_uniq p : 
  uniq (lfsp_tseq p).
Proof. rewrite /lfsp_tseq (map_inj_uniq val_inj); exact/tseq_uniq. Qed.

Lemma mem_lfsp_tseq p : 
  lfsp_tseq p =i finsupp p.
Proof. 
  rewrite /lfsp_tseq=> e.
  apply/idP/idP.
  - by move=> /mapP [e'] + ->; case: e'.
  move=> in_supp; apply/mapP.
  exists (Sub e in_supp)=> //.
  by rewrite mem_tseq fintype.mem_enum. 
Qed.

Lemma lfsp_idx_lt p e :
  e \in finsupp p -> lfsp_idx p e < #|`finsupp p|.
Proof. 
  rewrite /lfsp_idx=> in_supp.
  rewrite -lfsp_tseq_size ltEnat /=. 
  by rewrite index_mem mem_lfsp_tseq.
Qed.  

Lemma lfsp_idx_le p e :
  lfsp_idx p e <= #|`finsupp p|.
Proof. 
  case: (e \in finsupp p)/idP.
  - by move=> /lfsp_idx_lt /ltW.
  move=> /negP Nin_supp.
  rewrite /lfsp_idx memNindex ?lfsp_tseq_size //.
  by rewrite mem_lfsp_tseq. 
Qed.

Lemma lfsp_event_inE p e0 n : 
  (lfsp_event p e0 n \in finsupp p) = (n < #|`finsupp p|).
Proof. 
  rewrite /lfsp_event -mem_lfsp_tseq -lfsp_tseq_size. 
  apply/idP/idP; last exact/mem_nth. 
  admit. 
Admitted.

Lemma lfsp_idxK p e0 :
  {in finsupp p, cancel (lfsp_idx p) (lfsp_event p e0)}. 
Proof. 
  rewrite /lfsp_idx /lfsp_event=> e eIn.
  by rewrite nth_index ?mem_lfsp_tseq.
Qed.

Lemma lfsp_eventK p e0 :
  {in (< #|` finsupp p|), cancel (lfsp_event p e0) (lfsp_idx p)}. 
Proof. 
  rewrite /lfsp_idx /lfsp_event=> n. 
  rewrite inE ltEnat=> nLe.
  rewrite index_uniq ?lfsp_tseq_size //.
  exact/lfsp_tseq_uniq.
Qed.

End Theory.
End Theory.

End lFsPrePoset.

Export lFsPrePoset.Def.
Export lFsPrePoset.Theory.


Module lFsPoset. 

Module Export Def.

Section Def. 
Context (E : identType) (L : eqType).
Variable (bot : L).

Structure lfsposet : Type := mk_lFsPoset {
  lfsposet_val :> lfspreposet E L bot ; 
  _ : let p := lfsposet_val in 
      [&& lab_defined p, supp_closed p & acyclic (fin_ica p)]
}.

Canonical lfsposet_subType := Eval hnf in [subType for lfsposet_val].

Implicit Types (p : lfsposet).

Lemma lfsp_lab_defined p : lab_defined p.
Proof. by move: (valP p)=> /and3P[]. Qed.

Lemma lfsp_supp_closed p : supp_closed p.
Proof. by move: (valP p)=> /and3P[]. Qed.

Lemma lfsp_acyclic p : acyclic (fin_ica p).
Proof. by move: (valP p)=> /and3P[]. Qed.

End Def.
End Def.

Arguments lfsposet E L bot : clear implicits.

Arguments fin_lab {E L bot} p.
Arguments fin_ica {E L bot} p.
Arguments fin_ca  {E L bot} p.
Arguments fin_sca {E L bot} p.

Module Export Instances.
Section Instances. 

Definition lfsposet_eqMixin E L bot := 
  Eval hnf in [eqMixin of (lfsposet E L bot) by <:].
Canonical lfinposet_eqType E L bot := 
  Eval hnf in EqType (lfsposet E L bot) (@lfsposet_eqMixin E L bot).

Definition lfsposet_choiceMixin E (L : choiceType) bot :=
  Eval hnf in [choiceMixin of (lfsposet E L bot) by <:].
Canonical lfsposet_choiceType E (L : choiceType) bot :=
  Eval hnf in ChoiceType (lfsposet E L bot) (@lfsposet_choiceMixin E L bot).

Definition lfsposet_countMixin E (L : countType) bot :=
  Eval hnf in [countMixin of (@lfsposet E L bot) by <:].
Canonical lfinposet_countType E (L : countType) bot :=
  Eval hnf in CountType (lfsposet E L bot) (@lfsposet_countMixin E L bot).

Canonical subFinfun_subCountType E (L : countType) bot :=
  Eval hnf in [subCountType of (lfsposet E L bot)].

End Instances.
End Instances.

Module Export POrder.
Section POrder.
Context {E : identType} {L : eqType}.
Variable (bot : L) (p : lfsposet E L bot).

Lemma fs_sca_def e1 e2 : 
  fs_sca p e1 e2 = (e2 != e1) && (fs_ca p e1 e2).
Proof. done. Qed.

Lemma fs_caP e1 e2 : 
  reflect ((fs_ica p : hrel E E)^* e1 e2) (fs_ca p e1 e2).
Proof. 
  (* TODO: try to simplify proof *)
  apply/equivP.  
  - apply/(equivP idP); apply: iff_trans.
    - by apply/rel_qmk_m.
    rewrite qmk_weq; last first.
    - move=> /= x y; rewrite /fs_ca.
      apply: iff_sym; apply: rwP.
      apply/sub_rel_liftP. 
    by apply: iff_refl. 
  apply: iff_trans=> /=. 
  - apply: or_iff_compat_l.
    apply/exists_equiv=> e1'.
    apply/exists_equiv=> e2'.
    (* TODO: make lemma? *)
    have H: forall A1 A2 B C, A1 <-> A2 -> [/\ A1, B & C] <-> [/\ A2, B & C].
    - move=> ???? [H1 H2]; split; move=> [???]; split=> //; [exact/H1|exact/H2].
    apply/H; apply: iff_sym. 
    apply: iff_trans; last first. 
    - apply: rwP; exact/(connect_strP).
    by apply/clos_rt_str.
  apply: iff_trans; last first.
  - by apply/clos_rt_str.
  move=> /=; split=> [[|[e1' [] e2' []]] |].
  - move=> ->; exact/rt_refl.
  - move=> + <- <-; elim=> //.
    + move=> ??; exact/rt_step.
    move=> ??? ? + ?; exact/rt_trans.
  elim=> //=.
  - move=> {}e1 {}e2 /[dup] /(supp_closedP _ (lfsp_supp_closed p)) /andP[].
    move=> Pe1 Pe2 ica; right; exists (Sub e1 Pe1), (Sub e2 Pe2).
    by split=> //; apply/rt_step.
  - by move=> ?; left.
  move=> ??? ? [-> ? [->|] | + ? [|]]. 
  - by left.
  - move=> [e1' [] e2' []] ???.
    by right; exists e1', e2'.
  - move=> [e1' [] e2' []] ??? <-.
    by right; exists e1', e2'.
  move=> [e1' [] e2' []] rt12 ??.
  move=> [e3' [] e4' []] rt34 ??.
  right; exists e1', e4'; split=> //=.
  apply/rt_trans; first exact/rt12. 
  suff: e2' = e3'=> [->|] //.
  apply/val_inj=> /=; congruence.
Qed.  
 
Lemma fs_ca_refl : 
  reflexive (fs_ca p). 
Proof. by move=> ?; apply/fs_caP/clos_rt_str/rt_refl. Qed. 

Lemma fs_ca_trans : 
  transitive (fs_ca p). 
Proof. 
  move=> y x z /fs_caP /clos_rt_str ca_xy /fs_caP /clos_rt_str ca_yz. 
  apply/fs_caP/clos_rt_str/rt_trans; [exact/ca_xy | exact/ca_yz].
Qed. 

Lemma fs_ca_antisym : 
  antisymmetric (fs_ca p). 
Proof. 
  move=> e1 e2 /andP[]; rewrite /fs_ca /=.
  rewrite /dhrel_one=> /orP[/eqP->|+ /orP[/eqP<-|]] //. 
  move=> /sub_rel_liftP + /sub_rel_liftP.
  move=> [e1' [] e2' [+++]] [e3' [] e4' [+++]].
  move=> /[swap] <- /[swap] <-.
  move=> ++ /val_inj H1 /val_inj H2.
  rewrite H2 H1=> con_e12 con_e21.
  suff: e1' = e2'=> [->|] //.
  apply/(connect_antisym (lfsp_acyclic p)).
  by apply/andP.
Qed.  

Definition lfsposet_porderMixin := 
  @LePOrderMixin E (fs_ca p) (fs_sca p) 
    fs_sca_def fs_ca_refl fs_ca_antisym fs_ca_trans. 

Definition lfsposet_porderType := 
  POrderType tt E lfsposet_porderMixin.

Definition lfsposet_lposetMixin := 
  @lPoset.lPoset.Mixin E L (POrder.class lfsposet_porderType) (fs_lab p).

Definition lfsposet_lposetType := 
  @lPoset.lPoset.Pack L E (lPoset.lPoset.Class lfsposet_lposetMixin).

End POrder.
End POrder.

Module Export FinPOrder.
Section FinPOrder.
Context {E : identType} {L : eqType}.
Variable (bot : L) (p : @lfsposet E L bot).

Lemma fin_sca_def e1 e2 : 
  fin_sca p e1 e2 = (e2 != e1) && (fin_ca p e1 e2).
Proof. done. Qed.

Lemma fin_ca_refl : 
  reflexive (fin_ca p).
Proof. exact/connect_refl. Qed.

Lemma fin_ca_antisym : 
  antisymmetric (fin_ca p).
Proof. exact/connect_antisym/(lfsp_acyclic p). Qed.

Lemma fin_ca_trans : 
  transitive (fin_ca p).
Proof. exact/connect_trans. Qed.

Lemma fin_disp : unit. 
Proof. exact: tt. Qed.

Definition lfsposet_fin_porderMixin := 
  @LePOrderMixin _ (fin_ca p) (fin_sca p) 
    fin_sca_def fin_ca_refl fin_ca_antisym fin_ca_trans. 

Definition lfsposet_fin_porderType := 
  POrderType fin_disp _ lfsposet_fin_porderMixin.

Definition lfsposet_FinPOrderType :=
  [finPOrderType of lfsposet_fin_porderType].

Definition lfsposet_fin_lposetMixin := 
  @lPoset.lPoset.Mixin _ L (POrder.class lfsposet_fin_porderType) (fin_lab p).

Definition lfsposet_fin_lposetType := 
  @lPoset.lPoset.Pack L (lfsposet_FinPOrderType) (lPoset.lPoset.Class lfsposet_fin_lposetMixin).

Definition lfsposet_lfinposetType :=
  let finCls := FinPOrder.class lfsposet_FinPOrderType in
  let cls := @lFinPoset.lFinPoset.Class _ L finCls lfsposet_fin_lposetMixin in
  @lFinPoset.lFinPoset.Pack L _ cls.

End FinPOrder.
End FinPOrder.

Module Export Syntax. 
Notation "[ 'Event' 'of' p ]" := (lfsposet_lposetType p)
  (at level 0, format "[ 'Event'  'of'  p ]") : form_scope.
Notation "[ 'FinEvent' 'of' p ]" := (lfsposet_lfinposetType p)
  (at level 0, format "[ 'FinEvent'  'of'  p ]") : form_scope.
End Syntax.

Module Export Theory.
Section Theory.
Context {E : identType} {L : eqType}.
Variable (bot : L).
Implicit Types (p q : @lfsposet E L bot).

Lemma fs_labE p (e : [Event of p]) : 
  lab e = fs_lab p e.  
Proof. done. Qed.

Lemma fs_caE p (e1 e2 : [Event of p]) : 
  e1 <= e2 = fs_ca p e1 e2.  
Proof. done. Qed.

Lemma fs_scaE p (e1 e2 : [Event of p]) : 
  e1 < e2 = fs_sca p e1 e2.  
Proof. done. Qed.

Lemma fin_labE p (e : [FinEvent of p]) : 
  lab e = fin_lab p e.  
Proof. done. Qed.

Lemma fin_caE p (e1 e2 : [FinEvent of p]) : 
  e1 <= e2 = fin_ca p e1 e2.  
Proof. done. Qed.

Lemma fin_scaE p (e1 e2 : [FinEvent of p]) : 
  e1 < e2 = fin_sca p e1 e2.  
Proof. done. Qed.

Lemma fs_rcov_fsupp p e :
  fs_rcov p e `<=` finsupp p.
Proof.
  apply/fsubsetPn=> [[e']] /=.
  move: (lfsp_supp_closed p)=> /supp_closedP. 
  by move=> /[apply] /andP[??] /negP.
Qed.

Lemma fs_lab_Nbot p e : 
  (fs_lab p e != bot) = (e \in finsupp p).
Proof. 
  rewrite mem_finsupp /fs_lab /=.
  move: (lfsp_lab_defined p)=> /lab_definedP labP.
  case: finsuppP=> //=.  
  - by rewrite xpair_eqE negb_and eq_refl.
  move: labP=> /[apply]; rewrite /fs_lab.
  case: (p e)=> l es //=.
  by rewrite xpair_eqE negb_and=> ->.
Qed.

Lemma fs_lab_bot p e : 
  (fs_lab p e == bot) = (e \notin finsupp p).
Proof. by rewrite -fs_lab_Nbot negbK. Qed.

(* Lemma fs_ica_Nsupp p e1 e2 :  *)
(*   e1 \notin finsupp p -> ~~ (fs_ica p e1 e2). *)
(* Proof.  *)
(*   apply/contra. *)
(*   move=> /negP ?; apply/negP. *)
(*   by rewrite -fs_lab_Nbot negbK. Qed. *)

Lemma fs_ica_irrefl p : 
  irreflexive (fs_ica p).
Proof. 
  move: (@fin_ica_mono _ _ _ p)=> /irreflexive_mono [mon _]. 
  move=> x; case: (x \in (finsupp p))/idP; last first.
  - rewrite /fs_ica /fs_rcov=> ? /=. 
    rewrite fsfun_dflt=> //=; exact/negP.
  move=> Px; have ->: x = val (Sub x Px : finsupp p) by done.
  apply/mon/irreflexiveP; move: (lfsp_acyclic p). 
  by rewrite acyclicE=> /andP[].
Qed.

Lemma lfsposet_eqP p q : 
  reflect (fs_lab p =1 fs_lab q /\ fs_ica p =2 fs_ica q) (p == q).
Proof. 
  apply/(equivP idP); split=> [/eqP->|[]] //.
  rewrite /fs_lab /fs_ica=> eq_lab eq_ica.
  apply/eqP/val_inj=> /=.
  apply/fsfunP=> e /=; apply/eqP.
  rewrite /eq_op=> /=; apply/andP; split.
  - by rewrite (eq_lab e).
  apply/fset_eqP=> e'.
  move: (eq_ica e' e)=> /=.
  by rewrite /fs_rcov.
Qed.

End Theory.
End Theory.

End lFsPoset.

Export lFsPoset.Def.
Export lFsPoset.Instances.
Export lFsPoset.Syntax.
Export lFsPoset.Theory.


Module Pomset.

Import lPoset.Syntax.
Import lFsPoset.Syntax.

Module Export Def.
Section Def.  
Context (E : identType) (L : choiceType).
Variable (bot : L).

Definition is_iso : rel (@lfsposet E L bot) := 
  fun p q => 
    ??|{ffun [FinEvent of p] -> [FinEvent of q] | lFinPoset.iso_pred}|.

(* TODO: generalize the proofs to arbitary `T -> T -> Type`? *)
Lemma is_iso_refl : reflexive is_iso.
Proof. 
  rewrite /is_iso=> p.
  apply/lFinPoset.fisoP; 
  exists; exact/[iso of idfun]. 
Qed.

Lemma is_iso_sym : symmetric is_iso.
Proof. 
  rewrite /is_iso=> p q.
  apply/idP/idP=> /lFinPoset.fisoP [f]; 
    apply/lFinPoset.fisoP; 
    (* TODO: [iso of ...] notation for inverse *)
    exists; exact/(lPoset.Iso.Build.inv f).
Qed.

Lemma is_iso_trans : transitive is_iso.
Proof. 
  rewrite /is_iso=> p q r.
  move=> /lFinPoset.fisoP [f] /lFinPoset.fisoP [g]. 
  apply/lFinPoset.fisoP. 
  exists; exact/[iso of g \o f].
Qed.

Canonical is_iso_eqv := EquivRel is_iso is_iso_refl is_iso_sym is_iso_trans.

Definition pomset := {eq_quot is_iso}.

Canonical pomset_quotType := [quotType of pomset].
Canonical pomset_eqType := [eqType of pomset].
Canonical pomset_choiceType := [choiceType of pomset].
Canonical pomset_eqQuotType := [eqQuotType is_iso of pomset].

Implicit Types (p : pomset).

Coercion lfsposet_of p : lfsposet E L bot := repr p.

End Def.
End Def.

Arguments pomset E L bot : clear implicits.

Module Export Theory.
Section Theory.
Context {E : identType} {L : choiceType}.
Variable (bot : L).
Implicit Types (p q : pomset E L bot).

Lemma finsupp_size_pi (p : lfsposet E L bot) : 
  #|` finsupp (\pi p : pomset E L bot)| = #|` finsupp p|.
Proof. admit. Admitted.

(* Lemma finsupp_size_iso (p q : lfsposet E L bot) :  *)
(*   is_iso p q -> #|` finsupp p| = #|` finsupp p|. *)
(* Proof. admit. Admitted. *)

(* Lemma pomset_iso_eq f p q : *)
(*   fs_lab p =1 (fs_lab q) \o f -> fs_ica p =2 relpre f (fs_ica q) -> p = q. *)
(* Proof. admit. Admitted. *)

(* Lemma pomset_eqP p q : *)
(*   reflect *)
(*     (* (exists f, {mono f : e / fin_lab p e >-> fin_lab q e} /\ {mono f : e1 e2 / fin_ica p e1 e2 >-> fin_ica q e1 e2}) *) *)
(*     (exists f, fs_lab p =1 (fs_lab q) \o f /\ fs_ica p =2 relpre f (fs_ica q)) *)
(*     (p == q). *)
(* Proof. *)
(*   rewrite eqquot_eqE /= /is_iso. *)
(*   apply/equivP; first exact/lFinPoset.fisoP. *)
(*   split=> [[f] | [f [Plab Pica]]]. *)
(*   - pose efresh := fresh_seq (finsupp q). *)
(*     have efresh_nIn : efresh \notin (finsupp q). *)
(*     + exact/fresh_seq_nmem. *)
(*     pose f' := fun e => odflt efresh (omap (val \o f) (insub e)). *)
(*     exists f'; split=> [e | e1 e2]; subst f'=> /=. *)
(*     + case: insubP=> [e' ? <-|] /=; last first. *)
(*       * rewrite -fs_lab_bot=> /eqP ->. *)
(*         by apply/esym/eqP; rewrite fs_lab_bot. *)
(*       have->: fs_lab p (fsval e') = fin_lab p e' by done. *)
(*       have->: fs_lab q (fsval (f e')) = fin_lab q (f e') by done. *)
(*       by rewrite -fin_labE -fin_labE (lab_preserving f).  *)
(*     case: insubP=> [e1' ? | nsupp] /=; last first. *)
(*     + have->: fs_ica p e1 e2 = false. *)
(*       * apply/negP; move: nsupp; apply/contraNnot. *)
(*         by move: (lfsp_supp_closed p)=> /supp_closedP /[apply] /andP[].  *)
(*       have->: fs_ica q efresh _ = false=> // ?. *)
(*       apply/negP; move: efresh_nIn; apply/contraNnot. *)
(*       by move: (lfsp_supp_closed q)=> /supp_closedP /[apply] /andP[].  *)
(*     case: insubP=> [e2' ? | nsupp] /=; last first. *)
(*     + have->: fs_ica p e1 e2 = false. *)
(*       * apply/negP; move: nsupp; apply/contraNnot. *)
(*         by move: (lfsp_supp_closed p)=> /supp_closedP /[apply] /andP[].  *)
(*       have->: fs_ica q _ efresh = false=> // ?. *)
(*       apply/negP; move: efresh_nIn; apply/contraNnot. *)
(*       by move: (lfsp_supp_closed q)=> /supp_closedP /[apply] /andP[].  *)
(*     move=> <- <-. *)
(*     have->: fs_ica p (fsval e1') (fsval e2') = fin_ica p e1' e2' by done. *)
(*     have->: fs_ica q (fsval (f e1')) (fsval (f e2')) = fin_ica q (f e1') (f e2') by done. *)
(*     admit.  *)
(*     (* by rewrite -fin_icaE -fin_icaE (ca_monotone f).  *) *)
(*   pose f' := fun e => *)
(*   eexists. exists f. *)
(*   admit. *)
(* Admitted. *)

End Theory.
End Theory.

Module Export nPomset.

Section Def.
Context (E : identType) (L : choiceType).
Variable (bot : L) (n : nat).

Structure npomset : Type := nPomset { 
  npom_val :> pomset E L bot; 
  _ : size (finsupp npom_val) == n;
}.

Canonical npomset_subType := Eval hnf in [subType for npom_val].

Implicit Type p : npomset.

Definition npomset_supp p : n.-tuple E := Tuple (valP p).

Lemma npomset_suppE p : npomset_supp p = finsupp p :> seq E.
Proof. done. Qed.

Lemma npomset_size p : size (finsupp p) = n.
Proof. exact/eqP/(valP p). Qed.

End Def.

Arguments npomset E L bot n : clear implicits.

Definition npomset_eqMixin E L bot n := 
  Eval hnf in [eqMixin of npomset E L bot n by <:].
Canonical npomset_eqType E L bot n := 
  Eval hnf in EqType _ (@npomset_eqMixin E L bot n).

Definition npomset_choiceMixin E L bot n := 
  Eval hnf in [choiceMixin of npomset E L bot n by <:].
Canonical npomset_choiceType E L bot n := 
  Eval hnf in ChoiceType _ (@npomset_choiceMixin E L bot n).

Section FinType.
Context (E : identType) (L : finType).
Variable (bot : L) (n : nat) (e0 : E).

Local Notation enc_ffun := 
  ({ffun 'I_n -> L} * {ffun 'I_n * 'I_n -> bool})%type.

Implicit Types (p : npomset E L bot n).
Implicit Types (f : enc_ffun).

Definition dec_event p : 'I_n -> E := 
  fun i => lfsp_event p e0 (val i).

Definition enc_event : n.-ident E -> 'I_n :=
  fun e => ord_of_ident e.

Definition enc_iso p : E -> E := 
  fun e => lfsp_event p e0 (encode e).

Definition dec_iso p : E -> E := 
  fun e => decode (lfsp_idx p e).

Lemma dec_eventK p e : 
  dec_event p (enc_event e) = enc_iso p e.
Proof. done. Qed.

Lemma enc_dec_isoK p e :
  e \in finsupp p -> enc_iso p (dec_iso p e) = e.
Proof. 
  rewrite /enc_iso /dec_iso=> ?.
  by rewrite decodeK lfsp_idxK //. 
Qed.

Lemma dec_enc_isoK p e :
  encode e < #|` finsupp p| -> dec_iso p (enc_iso p e) = e.
Proof. 
  rewrite /enc_iso /dec_iso=> ?.
  rewrite lfsp_eventK ?encodeK //.
Qed.

Definition enc_lab p : {ffun 'I_n -> L} :=
  [ffun i => fs_lab p (dec_event p i)].

Definition enc_ica p : {ffun 'I_n * 'I_n -> bool} :=
  [ffun ij => fs_ica p (dec_event p ij.1) (dec_event p ij.2)].

Definition enc p : enc_ffun := 
  (enc_lab p, enc_ica p).

Lemma enc_labD p i :
  enc_lab p i != bot.
Proof. 
  rewrite /enc_lab /dec_event ffunE.
  apply/lab_definedP.
  - exact/lfsp_lab_defined.
  rewrite lfsp_event_inE npomset_size.
  exact/(valP i).
Qed.

(* Lemma enc_icaE p e1 e2 :  *)
(*   (enc_ica p) (ord_of_ident e1, ord_of_ident e2) = fs_ica p e1 e2. *)
(* Proof. admit. Admitted. *)

Definition dec_lab f : n.-ident E -> L :=
  fun e => f.1 (enc_event e).

Definition dec_ica f : rel (n.-ident E) :=
  fun e1 e2 => f.2 (enc_event e1, enc_event e2).

Definition predec f : lfspreposet E L bot := 
  lFsPrePoset.build bot (dec_lab f) (dec_ica f).

Let predec_enc p := predec (enc p).

Definition dec f : option (npomset E L bot n) := 
  let opomset := omap \pi (insub (predec f)) in
  obind insub opomset.

Lemma predec_enc_in_finsupp p e : 
  (e \in finsupp (predec_enc p)) = ((enc_iso p e) \in finsupp p).
Proof. 
  rewrite /predec /enc /lFsPrePoset.build. 
  move: (lfsp_lab_defined p)=> labD.
  rewrite finsupp_fset !in_fset !inE in_fsetval /=.
  rewrite /enc_iso lfsp_event_inE npomset_size.
  case: insubP=> [|/negPf->] //.
  move=> e' -> vale /=. 
  rewrite xpair_eqE negb_and. 
  apply/idP/idP=> //; apply/orP; left.
  rewrite /dec_lab /enc_lab /dec_event /enc_event ffunE.
  move: labD => /lab_definedP -> //.
  by rewrite lfsp_event_inE npomset_size (valP e').
Qed.

Lemma in_finsupp_predec_enc p e :
  e \in finsupp p -> (dec_iso p e) \in finsupp (predec_enc p).
Proof. by move=> ?; rewrite predec_enc_in_finsupp enc_dec_isoK. Qed.

Lemma encode_finsupp p e : 
  e \in finsupp (predec_enc p) -> encode e < n.
Proof. 
  rewrite predec_enc_in_finsupp /enc_iso.
  by rewrite lfsp_event_inE npomset_size. 
Qed.

Definition event_of p : finsupp (predec_enc p) -> (finsupp p) := 
  fun e => 
    let e' := enc_iso p (val e) in
    Sub e' (eqb_cast (predec_enc_in_finsupp p (val e)) (valP e)). 

Definition of_event p : (finsupp p) -> finsupp (predec_enc p) :=
  fun e =>
    let e' := dec_iso p (val e) in
    Sub e' (in_finsupp_predec_enc (valP e)).

Lemma event_ofK p : 
  cancel (@event_of p) (@of_event p).
Proof.
  rewrite /event_of /of_event=> e.
  apply/val_inj=> /=.
  rewrite dec_enc_isoK ?npomset_size //. 
  exact/encode_finsupp.
Qed.

Lemma of_eventK p : 
  cancel (@of_event p) (@event_of p).
Proof.
  rewrite /event_of /of_event=> e.
  apply/val_inj=> /=.
  by rewrite enc_dec_isoK.
Qed.

Lemma event_of_bij p :
  bijective (@event_of p).
Proof. exists (@of_event p); [exact/event_ofK | exact/of_eventK]. Qed.

Lemma fin_lab_mono p :
  { mono (@event_of p) : e /
    fin_lab (predec_enc p) e >-> fin_lab p e }.
Proof. 
  move=> e /=.
  rewrite /predec_enc /predec /enc.
  rewrite /fin_lab=> /=.
  rewrite lFsPrePoset.build_lab /=.
  rewrite /sub_lift !insubT /=.
  - exact/encode_finsupp/(valP e).
  rewrite /dec_lab /enc_lab /= => ?.
  by rewrite !ffunE. 
Qed.  

Lemma fin_ica_mono p :
  { mono (@event_of p) : e1 e2 /
    fin_ica (predec_enc p) e1 e2 >-> fin_ica p e1 e2 }.
Proof.
  move=> e1 e2 /=.
  rewrite /predec_enc /predec /enc.
  rewrite /fin_ica /sub_rel_down=> /=.
  rewrite lFsPrePoset.build_ica /=.
  rewrite /sub_rel_lift /= !insubT.
  - exact/encode_finsupp/(valP e1).
  - exact/encode_finsupp/(valP e2).
  rewrite /dec_ica /enc_ica /= => ??.
  by rewrite !ffunE. 
Qed.

Lemma fin_ca_mono p :
  { mono (@event_of p) : e1 e2 /
    fin_ca (predec_enc p) e1 e2 >-> fin_ca p e1 e2 }.
Proof. 
  rewrite /fin_ca=> e1 e2 /=.
  apply/connect_mono.
  - exact/event_of_bij.
  exact/fin_ica_mono.
Qed.

Lemma predec_enc_lab_defined p : 
  lab_defined (predec_enc p).
Proof. 
  apply/lab_definedP=> e.
  rewrite lFsPrePoset.build_lab /=.
  rewrite lFsPrePoset.build_finsupp; last first.
  + move=> e' /=; rewrite /dec_lab ffunE. 
    rewrite fs_lab_Nbot lfsp_event_inE npomset_size.
    exact(valP (ord_of_ident e')).
  rewrite !in_fsetval=> eIn. 
  rewrite sub_liftT=> /=.
  - move: eIn; case: insubP=> //.
  move=> ? /=; exact/enc_labD. 
Qed.

Lemma predec_enc_supp_closed p : 
  supp_closed (predec_enc p).
Proof. 
  apply/supp_closedP=> e1 e2.
  rewrite lFsPrePoset.build_ica /=.
  rewrite lFsPrePoset.build_finsupp; last first.
  + move=> e /=; rewrite /dec_lab ffunE. 
    rewrite fs_lab_Nbot lfsp_event_inE npomset_size.
    exact(valP (ord_of_ident e)).
  rewrite !in_fsetval=> /sub_rel_lift_fld /=.
  by move=> /andP[??]; rewrite !insubT.   
Qed.

Lemma predec_enc_acyclic p : 
  acyclic (fin_ica (predec_enc p)).
Proof.
  move: (event_of_bij p) (@fin_ica_mono p)=> + /[dup] mon. 
  move=> /connect_mono /[apply] cmon.
  rewrite acyclicE; apply/andP; split.
  - apply/irreflexiveP/(irreflexive_mono mon) => x /=.
    rewrite /fin_ica /sub_rel_down /=.
    exact/fs_ica_irrefl.
  apply/antisymmetricP/(antisymmetric_mono cmon) => x y /= ?.
  apply/(bij_inj (event_of_bij p)).
  by apply/lFsPoset.FinPOrder.fin_ca_antisym.
Qed.    

Lemma npomset_encK : pcancel enc dec. 
Proof. 
  move=> p; rewrite /dec.
  rewrite insubT; [apply/and3P; split|].
  - exact/predec_enc_lab_defined.
  - exact/predec_enc_supp_closed.
  - exact/predec_enc_acyclic.
  move=> Pp /=; rewrite insubT.
  - rewrite finsupp_size_pi /=.
    rewrite -(npomset_size p) !cardfE.  
    apply/eqP/bij_eq_card.
    exact/event_of_bij.
  move=> SZp; congr Some.
  apply/val_inj=> /=.
  rewrite -(reprK (val p)); apply/eqquotP.
  apply/lFinPoset.fisoP=> /=.
  eexists; exists (@event_of p).
  (* TODO: refactor --- do not expose internals of Iso.class_of !!! *)
  repeat constructor.
  - exact/fin_lab_mono.
  - by move=> ??; rewrite !fin_caE fin_ca_mono.
  - exists (@of_event p); [exact/event_ofK | exact/of_eventK].
  by move=> ??; rewrite !fin_caE fin_ca_mono.
Qed.

End FinType.

End bPomset.

Module Export Hom.
Module Export POrder.

Import lFsPoset.Syntax.

Section POrder.
Context {E : identType} {L : choiceType} (eps : L).
Implicit Types (p q : pomset E L eps).

Definition bhom_le : rel (pomset E L eps) := 
  fun p q => 
    let EP := [FinEvent of (repr p)] in
    let EQ := [FinEvent of (repr q)] in
    ??|{ffun EP -> EQ | lFinPoset.bhom_pred}|.

Definition bhom_lt : rel (pomset E L eps) := 
  fun p q => (q != p) && (bhom_le p q).

Lemma bhom_lt_def p q : bhom_lt p q = (q != p) && (bhom_le p q).
Proof. done. Qed.

Lemma bhom_le_refl : reflexive bhom_le. 
Proof. move=> ?; exact/lFinPoset.bhom_refl. Qed.

Lemma bhom_le_trans : transitive bhom_le. 
Proof. move=> ???; exact/lFinPoset.bhom_trans. Qed.

(* TODO: move part of the proof to lposet.v ? *)
Lemma bhom_le_antisym : antisymmetric bhom_le. 
Proof. 
  move=> p q /andP[] /lFinPoset.fbhomP[f] /lFinPoset.fbhomP[g].
  (* TODO: make lemma: reflect (x = y) (e (repr x) (repr y)) ? *)
  rewrite -(reprK p) -(reprK q).
  apply/eqP=> /=; rewrite /pomset eqmodE /=.
  apply/lFinPoset.fisoP=> /=.
  exists; exact/(lFinPoset.of_ihoms f g).   
Qed.

Lemma disp : unit. 
Proof. exact: tt. Qed.

Definition pomset_bhomPOrderMixin := 
  @LePOrderMixin _ bhom_le bhom_lt 
    bhom_lt_def bhom_le_refl bhom_le_antisym bhom_le_trans. 

Canonical pomset_bhomPOrderType := 
  POrderType disp (pomset E L eps) pomset_bhomPOrderMixin.

Lemma bhom_leE p q : le p q = bhom_le p q.
Proof. done. Qed.

Lemma bhom_ltE p q : lt p q = bhom_lt p q.
Proof. done. Qed.

End POrder.
End POrder.
End Hom.

End Pomset.

Export Pomset.Def.
(* Export Pomset.Theory. *)
Export Pomset.Hom.POrder.

(* Context (E : identType) (L : choiceType). *)
(* Variable (bot : L). *)
(* Variables (p q : pomset E L bot). *)
(* Variables (e1 e2 : E). *)
(* Check (e1 <= e2 :> [Event of p]). *)
(* Check (e1 <= e2 :> [Event of q]). *)
(* Check (p <= q). *)
