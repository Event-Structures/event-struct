From Coq Require Import Relations.
From RelationAlgebra Require Import lattice monoid rel boolean.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From mathcomp Require Import eqtype choice order fintype fingraph finmap.
From mathcomp Require Import generic_quotient.
From mathcomp.tarjan Require Import extra acyclic. 
From eventstruct Require Import utils relalg inhtype ident lposet.

(******************************************************************************)
(* This file provides a theory of pomset languages.                           *)
(* TODO                                                                       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.
Import Order.LTheory.

Local Open Scope order_scope.
Local Open Scope quotient_scope.
Local Open Scope ra_terms.
Local Open Scope lposet_scope.

Declare Scope pomset_scope.
Delimit Scope pomset_scope with pomset.

Local Open Scope pomset_scope.

(* TODO: move to appropriate place *)
Notation fsupp := finsupp.

Module lFsPoset. 

Module Export Def.

Notation lfspreposet E L eps := ({ fsfun E -> (L * seq E) of e => (eps, [::]) }).

Section Def. 
Context (E : identType) (L : eqType).
Variable (eps : L).

Implicit Types (p : lfspreposet E L eps).

Definition fs_lab p : E -> L := 
  fun e => (p e).1. 

Definition fin_lab p : fsupp p -> L := 
  fun e => fs_lab p (val e).

Definition fs_rcov p : E -> seq E := 
  fun e => (p e).2. 

Definition fs_ica p : rel E := 
  [rel x y | grel (fs_rcov p) y x]. 

Definition fin_ica p : rel (fsupp p) := 
  sub_rel_down (fs_ica p).

Definition fin_ca p : rel (fsupp p) := 
  connect (@fin_ica p).

Definition fin_sca p : rel (fsupp p) := 
  fun e1 e2 => (e2 != e1) && (@fin_ca p e1 e2).

Definition fs_ca p : rel E := 
  (sub_rel_lift (@fin_ca p) : {dhrel E & E})^?.

Definition fs_sca p : rel E := 
  fun e1 e2 => (e2 != e1) && (fs_ca p e1 e2).

Definition supp_closed q := 
  [forall e : finsupp q, all (fun e' => e' \in finsupp q) (fs_rcov q (val e))].

Lemma supp_closedP q : 
  reflect (forall e1 e2, fs_ica q e1 e2 -> (e1 \in fsupp q) && (e2 \in fsupp q))
          (supp_closed q).
Proof. 
  rewrite /supp_closed /fs_ica /fs_rcov. 
  apply/(equivP forallP); split=> /=; last first.
  - move=> ica_supp; case=> e2 in_supp /=. 
    by apply/allP=> e1 /ica_supp /andP[].
  move=> all_supp e1 e2 /=.
  case: (in_fsetP (finsupp q) e2)=> [e2'|].
  - by move: (all_supp e2')=> /allP /[swap] /= <- /[apply] ->.
  by move=> /fsfun_dflt -> //.
Qed.

Structure lfsposet : Type := lFsPoset {
  lfsposet_val :> { fsfun E -> (L * seq E) of e => (eps, [::]) } ; 
  _ : let p := lfsposet_val in 
      supp_closed p && acyclic (@fin_ica p)
}.

Canonical lfsposet_subType := Eval hnf in [subType for lfsposet_val].

Lemma lfsposet_supp (p : lfsposet) : supp_closed p.
Proof. by move: (valP p)=> /andP[]. Qed.

Lemma lfsposet_acyclic (p : lfsposet) : acyclic (@fin_ica p).
Proof. by move: (valP p)=> /andP[]. Qed.

End Def.
End Def.

Arguments lfsposet E L eps : clear implicits.

Arguments fin_lab {E L eps} p.
Arguments fin_ica {E L eps} p.
Arguments fin_ca  {E L eps} p.
Arguments fin_sca {E L eps} p.

Module Export Instances.
Section Instances. 

Definition lfsposet_eqMixin E L eps := 
  Eval hnf in [eqMixin of (lfsposet E L eps) by <:].
Canonical lfinposet_eqType E L eps := 
  Eval hnf in EqType (lfsposet E L eps) (@lfsposet_eqMixin E L eps).

Definition lfsposet_choiceMixin E (L : choiceType) eps :=
  Eval hnf in [choiceMixin of (lfsposet E L eps) by <:].
Canonical lfsposet_choiceType E (L : choiceType) eps :=
  Eval hnf in ChoiceType (lfsposet E L eps) (@lfsposet_choiceMixin E L eps).

(* TODO: define missing count mixin and canonical instances for fsfun? *)

(* Definition lfsposet_countMixin E (L : countType) eps := *)
(*   Eval hnf in [countMixin of (@lfsposet E L eps) by <:]. *)
(* Canonical lfinposet_countType E (L : countType) := *)
(*   Eval hnf in CountType (lfinposet E L) (lfinposet_countMixin E L). *)

(* Canonical subFinfun_subCountType E (L : countType) := *)
(*   Eval hnf in [subCountType of (lfinposet E L)]. *)

(* Definition lfinposet_finMixin E (L : finType) := *)
(*   Eval hnf in [finMixin of (lfinposet E L) by <:]. *)
(* Canonical lfinposet_finType E (L : finType) := *)
(*   Eval hnf in FinType (lfinposet E L) (lfinposet_finMixin E L). *)

(* Canonical lfinposet_subFinType E (L : finType) := *)
(*   Eval hnf in [subFinType of (lfinposet E L)]. *)

End Instances.
End Instances.

Module Export POrder.
Section POrder.
Context {E : identType} {L : eqType}.
Variable (eps : L) (p : lfsposet E L eps).

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
    - by move=> ???? ->.  
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
  - move=> {}e1 {}e2 /[dup] /(supp_closedP _ (lfsposet_supp p)) /andP[].
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
  apply/(connect_antisym (lfsposet_acyclic p)).
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
Variable (eps : L) (p : @lfsposet E L eps).

Lemma fin_sca_def e1 e2 : 
  fin_sca p e1 e2 = (e2 != e1) && (fin_ca p e1 e2).
Proof. done. Qed.

Lemma fin_ca_refl : 
  reflexive (fin_ca p).
Proof. exact/connect_refl. Qed.

Lemma fin_ca_antisym : 
  antisymmetric (fin_ca p).
Proof. exact/connect_antisym/(lfsposet_acyclic p). Qed.

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
Variable (eps : L).
Implicit Types (p : @lfsposet E L eps).

Lemma fs_labE p (e : [Event of p]) : 
  lab e = fs_lab p e.  
Proof. done. Qed.

Lemma fs_caE p (e1 e2 : [Event of p]) : 
  ca e1 e2 = fs_ca p e1 e2.  
Proof. done. Qed.

Lemma fs_scaE p (e1 e2 : [Event of p]) : 
  sca e1 e2 = fs_sca p e1 e2.  
Proof. done. Qed.

End Theory.
End Theory.

End lFsPoset.

Export lFsPoset.Def.
Export lFsPoset.Instances.
Export lFsPoset.Theory.


Module Pomset.

Import lPoset.Syntax.
Import lFsPoset.Syntax.

Module Export Def.
Section Def.  
Context (E : identType) (L : choiceType).
Variable (eps : L).

Definition is_iso : rel (@lfsposet E L eps) := 
  fun p q => 
    ??|{ffun [FinEvent of p] -> [FinEvent of q] | lFinPoset.iso_pred}|.

(* TODO: generalize the proofs to arbitary `T -> T -> Type`? *)
Lemma is_iso_refl : reflexive is_iso.
Proof. 
  rewrite /is_iso=> p.
  apply/lFinPoset.fisoP. 
  exists; exact/lPoset.Iso.id.
Qed.

Lemma is_iso_sym : symmetric is_iso.
Proof. 
  rewrite /is_iso=> p q.
  apply/idP/idP=> /lFinPoset.fisoP [f]; 
    apply/lFinPoset.fisoP; 
    exists; exact/(lPoset.Iso.inv f).
Qed.

Lemma is_iso_trans : transitive is_iso.
Proof. 
  rewrite /is_iso=> p q r.
  move=> /lFinPoset.fisoP [f] /lFinPoset.fisoP [g]. 
  apply/lFinPoset.fisoP. 
  exists; exact/(lPoset.Iso.comp f g).
Qed.

Canonical is_iso_eqv := EquivRel is_iso is_iso_refl is_iso_sym is_iso_trans.

Definition pomset := {eq_quot is_iso}.

Canonical pomset_quotType := [quotType of pomset].
Canonical pomset_eqType := [eqType of pomset].
Canonical pomset_choiceType := [choiceType of pomset].
Canonical pomset_eqQuotType := [eqQuotType is_iso of pomset].

Implicit Types (p : pomset).

(* TODO: try `simpl_fun` & `simpl_rel` ? *)
Definition pom_lab p : E -> L := 
  fs_lab (repr p).

Definition pom_ica  p : rel E := 
  fs_ica (repr p).

Definition pom_ca  p : rel E := 
  fs_ca (repr p).

Definition pom_sca p : rel E := 
  fs_sca (repr p).

End Def.
End Def.

Arguments pomset E L eps : clear implicits.

Module Export POrder.
Section POrder.
Context {E : identType} {L : choiceType}.
Variable (eps : L) (p : pomset E L eps).

Lemma pom_sca_def e1 e2 : pom_sca p e1 e2 = (e2 != e1) && (pom_ca p e1 e2).
Proof. rewrite /pom_sca /pom_ca; exact/lFsPoset.POrder.fs_sca_def. Qed.

Lemma pom_ca_refl : reflexive (pom_ca p). 
Proof. move=> ? /=; rewrite /pom_ca; exact/lFsPoset.POrder.fs_ca_refl. Qed.

Lemma pom_ca_antisym : antisymmetric (pom_ca p). 
Proof. move=> ?? /=; rewrite /pom_ca; exact/lFsPoset.POrder.fs_ca_antisym. Qed.

Lemma pom_ca_trans : transitive (pom_ca p). 
Proof. move=> ??? /=; rewrite /pom_ca; exact/lFsPoset.POrder.fs_ca_trans. Qed.

Definition pomset_porderMixin := 
  @LePOrderMixin E (pom_ca p) (pom_sca p) 
    pom_sca_def pom_ca_refl pom_ca_antisym pom_ca_trans. 

Definition pomset_porderType := 
  POrderType tt E pomset_porderMixin.

Definition pomset_lposetMixin := 
  @lPoset.lPoset.Mixin E L (POrder.class pomset_porderType) (pom_lab p).

Definition pomset_lposetType := 
  @lPoset.lPoset.Pack L E (lPoset.lPoset.Class pomset_lposetMixin).

End POrder.
End POrder.

Module Export FinPOrder.
Section FinPOrder.
Context {E : identType} {L : choiceType}.
Variable (eps : L) (p : pomset E L eps).

Local Notation fsupp := (fsupp (repr p)).

Definition pom_fin_lab : fsupp -> L := 
  fin_lab (repr p).

Definition pom_fin_ica : rel fsupp := 
  fin_ica (repr p).

Definition pom_fin_ca : rel fsupp := 
  fin_ca (repr p).

Definition pom_fin_sca : rel fsupp := 
  fin_sca (repr p).

Lemma fin_sca_def e1 e2 : pom_fin_sca e1 e2 = (e2 != e1) && (pom_fin_ca e1 e2).
Proof. done. Qed.

Lemma fin_ca_refl : reflexive pom_fin_ca.
Proof. exact/lFsPoset.FinPOrder.fin_ca_refl. Qed.

Lemma fin_ca_antisym : antisymmetric pom_fin_ca.
Proof. exact/lFsPoset.FinPOrder.fin_ca_antisym. Qed.

Lemma fin_ca_trans : transitive pom_fin_ca.
Proof. exact/lFsPoset.FinPOrder.fin_ca_trans. Qed.

Lemma fin_disp : unit. 
Proof. exact: tt. Qed.

Definition pomset_fin_porderMixin := 
  @LePOrderMixin _ pom_fin_ca pom_fin_sca 
    fin_sca_def fin_ca_refl fin_ca_antisym fin_ca_trans. 

Definition pomset_fin_porderType := 
  POrderType fin_disp _ pomset_fin_porderMixin.

Definition pomset_FinPOrderType :=
  [finPOrderType of pomset_fin_porderType].

Definition pomset_fin_lposetMixin := 
  @lPoset.lPoset.Mixin _ L (POrder.class pomset_fin_porderType) pom_fin_lab.

Definition pomset_fin_lposetType := 
  let cls := lPoset.lPoset.Class pomset_fin_lposetMixin in 
  @lPoset.lPoset.Pack L (pomset_FinPOrderType) cls.

Definition pomset_lfinposetType :=
  let finCls := FinPOrder.class pomset_FinPOrderType in
  let cls := @lFinPoset.lFinPoset.Class _ L finCls pomset_fin_lposetMixin in
  @lFinPoset.lFinPoset.Pack L _ cls.

End FinPOrder.
End FinPOrder.

Module Export Syntax. 
Notation "[ 'Event' 'of' p ]" := (pomset_lposetType p)
  (at level 0, format "[ 'Event'  'of'  p ]") : form_scope.
Notation "[ 'FinEvent' 'of' p ]" := (pomset_lfinposetType p)
  (at level 0, format "[ 'FinEvent'  'of'  p ]") : form_scope.
End Syntax.

Module Export Theory.
Section Theory.
Context {E : identType} {L : choiceType}.
Variable (eps : L).
Implicit Types (p : pomset E L eps).

Lemma pom_labE p (e : [Event of p]) : 
  lab e = fs_lab (repr p) e.  
Proof. done. Qed.

Lemma pom_caE p (e1 e2 : [Event of p]) : 
  ca e1 e2 = fs_ca (repr p) e1 e2.  
Proof. done. Qed.

Lemma pom_scaE p (e1 e2 : [Event of p]) : 
  sca e1 e2 = fs_sca (repr p) e1 e2.  
Proof. done. Qed.

End Theory.
End Theory.

End Pomset.
