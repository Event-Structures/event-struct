From Coq Require Import Relations.
From RelationAlgebra Require Import lattice monoid rel boolean.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat seq tuple.
From mathcomp Require Import eqtype choice order generic_quotient.
From mathcomp Require Import fintype finfun finset fingraph finmap.
From mathcomp.tarjan Require Import extra acyclic kosaraju acyclic_tsorted. 
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

Import Order.LTheory.

Local Open Scope order_scope.
Local Open Scope fset_scope.
Local Open Scope quotient_scope.
Local Open Scope ra_terms.
Local Open Scope lposet_scope.

Declare Scope pomset_scope.
Delimit Scope pomset_scope with pomset.

Local Open Scope pomset_scope.


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
  [forall e : finsupp p, fs_rcov p (val e) `<=` finsupp p].

Definition lfsp_tseq p : seq E := 
  map val (tseq (rgraph (@fin_ica p))).

Definition lfsp_idx p : E -> nat := 
  fun e => index e (lfsp_tseq p). 

Definition lfsp_event p e0 : nat -> E := 
  fun n => nth e0 (lfsp_tseq p) n.

Definition lfsp_labels p : seq L := 
  map (fs_lab p) (lfsp_tseq p).

End Def.

Arguments fs_lab {E L bot} p.
Arguments fs_ica {E L bot} p.
Arguments fs_sca {E L bot} p.
Arguments fs_ca  {E L bot} p.

Arguments fin_lab {E L bot} p.
Arguments fin_ica {E L bot} p.
Arguments fin_sca {E L bot} p.
Arguments fin_ca  {E L bot} p.

End Def.

Section Build.
Context {E : identType} {L : eqType}.
Variable (bot : L). 
Implicit Types (p : lfspreposet E L bot).
Implicit Types (fE : {fset E}) (ls : seq L).

Definition build {fE} (lab : fE -> L) (ica : rel fE) : lfspreposet E L bot := 
  let rcov e := [fsetval e' in rgraph [rel x y | ica y x] e] in
  [fsfun e => (lab e, rcov e)].

Lemma build_finsupp {fE} lab ica : (forall e, lab e != bot) ->
  finsupp (@build fE lab ica) = fE.
Proof.
  move=> labB; apply/fsetP=> ?.
  rewrite mem_finsupp fsfun_ffun.
  case: insubP=> [*|/negbTE-> /[! eqxx] //].
  by rewrite xpair_eqE (negbTE (labB _)).
Qed. 

Lemma build_lab {fE} lab ica : 
  fs_lab (@build fE lab ica) =1 sub_lift (fun=> bot) lab.
Proof.
  rewrite /fs_lab /sub_lift=> ?.
  rewrite fsfun_ffun; by case: insubP.
Qed.

Lemma build_ica {fE} lab ica : 
  fs_ica (@build fE lab ica) =2 sub_rel_lift ica.
Proof.
  rewrite /fs_ica /build /sub_rel_lift /fs_rcov=>> /=.
  rewrite fsfun_ffun. (do 2 case: insubP=> //=)=> [u ?<- v*|+*].
  - rewrite ?inE; exact/rgraphK.
  by rewrite in_fsetval_seq; case: insubP=> // ? ->.
Qed.

Definition of_seq ls := 
  let fE  := [fset e | e in nfresh ident0 (size ls) : seq E] in 
  let lab := fun e : fE => (nth bot ls (encode (val e))) in
  let ca := fun e1 e2 : fE => (val e1) <=^i (val e2) in
  @build fE lab (cov ca). 

Lemma of_seq_lab ls e : 
  fs_lab (of_seq ls) e = nth bot ls (encode e).
Proof.
  rewrite /of_seq build_lab /= /sub_lift.
  case: insubP=> /= [?? ->|] //.
  rewrite !in_fset /mem_fin /=.
  rewrite in_nfresh encode0 addn0. 
  rewrite negb_and ltnNge negbK -ltnNge ltn0 orFb. 
  by move=> ?; rewrite nth_default.
Qed.

Lemma of_seq_ica ls e1 e2 : 
  let n := size ls in
  fs_ica (of_seq ls) e1 e2 = [&& e1 <=^i e2, e1 <^i (decode n) & e1 <^i (decode n)].
Proof. admit. Admitted.

End Build.

Module Export Theory.
Section Theory.
Context (E : identType) (L : eqType).
Variable (bot : L).
Implicit Types (p : lfspreposet E L bot).

Lemma lab_definedP p : 
  reflect {in finsupp p, forall e, fs_lab p e != bot} (lab_defined p).
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
            (e1 \in finsupp p) * (e2 \in finsupp p))
          (supp_closed p).
Proof. 
  rewrite /supp_closed /fs_ica /fs_rcov. 
  apply/(equivP forallP); split=> /=; last first.
  - move=> ica_supp; case=> e2 in_supp /=. 
    by apply/fsubsetP=> e1 /ica_supp [].
  move=> all_supp e1 e2 /=.
  case: (in_fsetP (finsupp p) e2)=> [e2'|].
  - by move: (all_supp e2')=> /fsubsetP /[swap] /= <- /[apply] ->.
  by move=> /fsfun_dflt -> //.
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

Structure lfsposet : Type := lFsPoset {
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

(* Definition lin p : pred (seq L) (* TODO: {fset (seq L)} *) *)
(*   fun ls => (of_seq ls : pomset E L bot) <= p. *)

(* Lemma bhom_lin p q : *)
(*   p <= q -> {subset (lin p) <= (lin q)}. *)

End Def.
End Def.

Arguments lfsposet E L bot : clear implicits.

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
  - move=> {}e1 {}e2 /[dup] /(supp_closedP _ (lfsp_supp_closed p))[].
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
  @lPoset.lPoset.Mixin E L (Order.POrder.class lfsposet_porderType) (fs_lab p).

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
  @lPoset.lPoset.Mixin _ L (Order.POrder.class lfsposet_fin_porderType) (fin_lab p).

Definition lfsposet_fin_lposetType := 
  @lPoset.lPoset.Pack L (lfsposet_FinPOrderType) (lPoset.lPoset.Class lfsposet_fin_lposetMixin).

Definition lfsposet_lfinposetType :=
  let finCls := Order.FinPOrder.class lfsposet_FinPOrderType in
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

Lemma fs_labE p : 
  lab =1 fs_lab p :> ([Event of p] -> L).  
Proof. done. Qed.

Lemma fs_caE p : 
  (<=%O) =2 fs_ca p :> rel [Event of p].  
Proof. done. Qed.

Lemma fs_scaE p : 
  (<%O) =2 fs_sca p :> rel [Event of p].  
Proof. done. Qed.

Lemma fin_labE p : 
  lab =1 fin_lab p :> ([FinEvent of p] -> L).  
Proof. done. Qed.

Lemma fin_caE p : 
  (<=%O) =2 fin_ca p :> rel [FinEvent of p].  
Proof. done. Qed.

Lemma fin_scaE p : 
  (<%O) =2 fin_sca p :> rel [FinEvent of p].  
Proof. done. Qed.

Lemma val_ca_mon p : 
  { homo (val : [FinEvent of p] -> [Event of p]) : e1 e2 / e1 <= e2 }.
Proof. 
  move=> x y; rewrite fin_caE fs_caE /fs_ca /=.
  by rewrite !sub_rel_lift_val=> ->.
Qed.

Lemma fs_lab_bot p e : 
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

Lemma fs_rcov_fsupp p e :
  {subset (fs_rcov p e) <= (finsupp p)}.
Proof.
  apply/fsubsetP/fsubsetPn=> [[e']] /=.
  move: (lfsp_supp_closed p)=> /supp_closedP. 
  by move=> /[apply][[->]].
Qed.

Lemma lfsposet_eqP p q : 
  reflect ((fs_lab p =1 fs_lab q) * (fs_ica p =2 fs_ica q)) (p == q).
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

Lemma lfsp_tseq_size p : 
  size (lfsp_tseq p) = #|`finsupp p|. 
Proof. by rewrite /lfsp_tseq size_map size_tseq cardfE. Qed.

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

Lemma bhom_leE p q : p <= q = bhom_le p q.
Proof. done. Qed.

Lemma bhom_ltE p q : p < q = bhom_lt p q.
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

Module Tomset.

Import lPoset.Syntax.
Import lFsPoset.Syntax.

Module Export Def.
Section Def.  
Context (E : identType) (L : choiceType).
Variable (bot : L).

Structure tomset : Type := mkTomset {
  tomset_val :> pomset E L bot;
  _ : totalb (fin_ca tomset_val); 
}.

Canonical tomset_subType := Eval hnf in [subType for tomset_val].

Implicit Types (t : tomset) (ls : seq L).

Lemma tomset_total t : 
  total (<=%O : rel [FinEvent of t]).
Proof. by move: (valP t)=> /totalP. Qed.

Lemma tomset_total_in t : 
  {in (finsupp t) &, total (<=%O : rel [Event of t])}.
Proof. 
  move=> x y xIn yIn.
  pose x' := (Sub x xIn) : [FinEvent of t].
  pose y' := (Sub y yIn) : [FinEvent of t].
  move: (tomset_total x' y'). 
  rewrite /x' /y'.
  by move=> /orP[|] /val_ca_mon /= ->. 
Qed.

End Def.
End Def.

Arguments tomset E L bot : clear implicits.

Module Export Theory.
Section Theory.
Context {E : identType} {L : choiceType}.
Variable (bot : L).
Implicit Types (t : tomset E L bot).

Lemma tomset_labelsK : 
  cancel (@lfsp_labels E L bot) (@lFsPrePoset.of_seq E L bot).
Proof. admit. Admitted.

End Theory.
End Theory.

End Tomset.


Export Tomset.Def.
Export Tomset.Theory.

