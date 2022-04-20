From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.
From mathcomp Require Import eqtype choice seq fintype finfun finmap zify.
From eventstruct Require Import utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fmap_scope.

Declare Scope perm_scope.
Delimit Scope perm_scope with perm.

Local Open Scope perm_scope.


Section FsFunBij.
Context {T : choiceType}.
Implicit Types (f : {fsfun T -> T}).

Lemma fsinj_bij f :
  injective f -> bijective f.
Proof.  
  move=> injf; apply/inj_surj_bij=> // x.
  pose S := finsupp f.
  have fS : forall a : S, f (val a) \in S.
  - by move: injf=> /(fsinjP 1 0) /= []. 
  pose ff : S -> S := (fun x => Sub (f (val x)) (fS x)).
  have injff: injective ff.
  - move=> {}x y; rewrite /ff /=. 
    by move=> /sub_inj/injf/val_inj.
  pose gg : S -> S := invF injff.
  case: (finsuppP f x)=> [xnin | xin].
  - by exists x; apply/fsfun_dflt.
  exists (val (gg (Sub x xin))).
  suff->: f (val (gg (Sub x xin))) = val (ff (gg (Sub x xin))).
  - by rewrite /gg f_invF. 
  by rewrite /ff /=.
Qed.  

End FsFunBij.


Module Export FPerm.

Section Def. 
Context (T : choiceType).

Structure fPerm : Type := mkPerm {
  fperm_val :> { fsfun T -> T for id }; 
  _ : fsinjectiveb fperm_val; 
}.

Canonical fperm_subType := Eval hnf in [subType for fperm_val].

Implicit Types (f : fPerm).

Lemma fperm_inj f : injective f.
Proof. exact/fsinjectiveP/valP. Qed.

Lemma fperm_bij f : bijective f.
Proof. exact/fsinj_bij/fperm_inj. Qed.

Lemma fperm_surj f : surjective f.
Proof. exact/bij_surj/fperm_bij. Qed.

Definition fperm_inv f := preim_of (fperm_surj f).

End Def.

Module Export Syntax. 
Notation "{ 'fperm' T }" := (@fPerm T) : type_scope.
End Syntax.

Section Instances.

Definition fperm_eqMixin (T : choiceType) := 
  Eval hnf in [eqMixin of {fperm T} by <:].
Canonical fperm_eqType (T : choiceType) := 
  Eval hnf in EqType {fperm T} (fperm_eqMixin T).

Definition fperm_choiceMixin (T : choiceType) := 
  Eval hnf in [choiceMixin of {fperm T} by <:].
Canonical fperm_choiceType (T : choiceType) := 
  Eval hnf in ChoiceType {fperm T} (fperm_choiceMixin T).

Definition fperm_countMixin (T : countType) := 
  Eval hnf in [countMixin of {fperm T} by <:].
Canonical fperm_countType (T : countType) := 
  Eval hnf in CountType {fperm T} (fperm_countMixin T).

Canonical fperm_subCountType (T : countType) := 
  Eval hnf in [subCountType of {fperm T}].

End Instances.

Section Theory.
Context (T : choiceType).
Implicit Types (f : {fperm T}).

Lemma fperm_invK f : cancel f (fperm_inv f).
Proof. exact/f_preim_of/fperm_inj. Qed.

Lemma inv_fpermK f : cancel (fperm_inv f) f.
Proof. exact/preim_of_f. Qed.

End Theory. 

End FPerm.
