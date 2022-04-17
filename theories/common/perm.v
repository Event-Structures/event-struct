From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.
From mathcomp Require Import eqtype choice seq fintype finfun finmap zify.
From eventstruct Require Import utils inhtype ident.

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


Module Export Permutation.

Section Def. 
Context (T : identType).

Structure perm : Type := mkPerm {
  perm_val :> { fsfun T -> T for id }; 
  _ : fsinjectiveb perm_val; 
}.

Canonical perm_subType := Eval hnf in [subType for perm_val].

Implicit Types (f : perm).

Lemma perm_inj f : injective f.
Proof. exact/fsinjectiveP/valP. Qed.

Lemma perm_bij f : bijective f.
Proof. exact/fsinj_bij/perm_inj. Qed.

Lemma perm_surj f : surjective f.
Proof. exact/bij_surj/perm_bij. Qed.

End Def.

Section Instances.
Context (T : identType).

Definition perm_eqMixin := Eval hnf in [eqMixin of (perm T) by <:].
Canonical perm_eqType := Eval hnf in EqType (perm T) perm_eqMixin.

Definition perm_choiceMixin := Eval hnf in [choiceMixin of (perm T) by <:].
Canonical perm_choiceType := Eval hnf in ChoiceType (perm T) perm_choiceMixin.

Definition perm_countMixin := Eval hnf in [countMixin of (perm T) by <:].
Canonical perm_countType := Eval hnf in CountType (perm T) perm_countMixin.

Canonical perm_subCountType := Eval hnf in [subCountType of (perm T)].

End Instances.
 
End Permutation.
