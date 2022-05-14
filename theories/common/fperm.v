From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.
From mathcomp Require Import eqtype choice seq fintype finfun finmap zify.
From eventstruct Require Import utils seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset_scope.
Local Open Scope fmap_scope.

Declare Scope perm_scope.
Delimit Scope perm_scope with perm.

Local Open Scope perm_scope.

Section FsFunInjb.
Context {T : choiceType}.
Implicit Types (f : {fsfun T -> T}) (X : {fset T}).

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

End FsFunInjb.


Module Export FPerm.

Section Def. 
Context (T : choiceType).

Structure fPerm : Type := mkPerm {
  fperm_val :> { fsfun T -> T for id }; 
  _ : fsinjectiveb fperm_val; 
}.

Canonical fperm_subType := Eval hnf in [subType for fperm_val].

Implicit Types (f : fPerm) (X : {fset T}).

Lemma fperm_inj f : injective f.
Proof. exact/fsinjectiveP/valP. Qed.

Lemma fperm_bij f : bijective f.
Proof. exact/fsinj_bij/fperm_inj. Qed.

Lemma fperm_surj f : surjective f.
Proof. exact/bij_surj/fperm_bij. Qed.

Definition fperm_inv f := preim_of (fperm_surj f).

Definition fperm0 : fPerm := 
  Sub [fsfun] (introT fsinjectiveP (fsfun0_inj (@inj_id T))).

(* The idea of implementation is due to Arthur Azevedo de Amorim
 * https://github.com/arthuraa/extructures/blob/master/theories/fperm.v
 * TODO: it would be nice to unify mathcomp/finmap & extructures eventually.
 *)
Definition mkfperm_fun (f : T -> T) X x := 
  let Y1  := (f @` X) `\` X in
  let Y2  := X `\` (f @` X) in
  if x \in Y1 then nth x Y2 (index x Y1) else f x.

Definition mkfperm_fsfun (f : T -> T) X : {fsfun T -> T} := 
  [fsfun x in X `|` (f @` X) => mkfperm_fun f X x].

Definition mkfperm (f : T -> T) X : fPerm :=
  odflt fperm0 (insub (mkfperm_fsfun f X)).

End Def.

Module Export Syntax. 

Notation "{ 'fperm' T }" := (@fPerm T) 
  (at level 0, format "{ 'fperm' T }") : type_scope.

Notation "[ 'fperm' ]" := (fperm0) 
  (at level 0, format "[ 'fperm' ]") : fun_scope.

Notation "[ 'fperm' x 'in' X => F ]" := (mkfperm (fun x => F) X)
  (at level 0, x at level 99, format "[ 'fperm'  x  'in'  X  =>  F ]") 
  : fun_scope.

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
Implicit Types (f : {fperm T}) (X : {fset T}).

Lemma fperm_invK f : cancel f (fperm_inv f).
Proof. exact/f_preim_of/fperm_inj. Qed.

Lemma inv_fpermK f : cancel (fperm_inv f) f.
Proof. exact/preim_of_f. Qed.

Lemma fperm_inv_inj f : injective (fperm_inv f).
Proof. exact/can_inj/inv_fpermK. Qed.

End Theory.

Section MkFPermTheory.
Context (T : choiceType).
Implicit Types (f : T -> T) (X : {fset T}).

Lemma mkfpermE f X : {in X &, injective f} -> 
  {in X, mkfperm f X =1 f}.
Proof. 
  move=> in_injf x xin.
  rewrite /mkfperm insubT /= => [|_]; last first.
  - by rewrite /mkfperm_fsfun /mkfperm_fun fsfunE !inE xin. 
  apply/fsinjectiveP/(fsinjP 2 0)=> /=.
  exists (X `|` (f @` X)). 
  - exact/finsupp_sub.
  clear x xin.
  pose Y1 := (f @` X) `\` X. 
  pose Y2 := X `\` (f @` X).
  pose D  := X `|` (f @` X).
  have szY : size Y1 = size Y2.
  - by rewrite !cardfsD fsetIC card_in_imfset.
  have nY1_X x : x \in D -> x \notin Y1 -> x \in X.
  - case/fsetUP=> //; by rewrite in_fsetD => ->; rewrite andbT negbK.
  have nth_Y2 x : x \in D -> x \in Y1 -> nth x Y2 (index x Y1) \in Y2.
  - move=> ??; by rewrite mem_nth // -szY index_mem.
  split; last first.
  - case=> /= x; rewrite /mkfperm_fsfun /mkfperm_fun fsfunE.
    move=> /[dup] xD ->; case: ifP.
    + by move=> /(nth_Y2 x xD); rewrite !inE=> /andP[_ ->].
    by move=> /negP/negP/(nY1_X x xD) ?; rewrite inE (in_imfset _ f).
  move=> x y xD yD; rewrite /mkfperm_fsfun /mkfperm_fun !fsfunE xD yD.
  case: ifP; case: ifP.
  - move: (@uniqP _ y Y2 (fset_uniq Y2))=> nth_injY2.
    move=> /[dup] yin + /[dup] xin; rewrite -!index_mem=> ysz xsz.
    rewrite (set_nth_default y x); last by rewrite -szY. 
    move=> /nth_injY2; rewrite !inE -szY=> idx_eq.
    by move: (idx_eq xsz ysz); apply/index_inj.
  - move=> /negP/negP /(nY1_X y yD) /(in_imfset imfset_key f) /= fy.
    by move=> /(nth_Y2 x xD) /[swap] ->; rewrite inE=> /andP[/negP]. 
  - move=> /[swap] /negP/negP /(nY1_X x xD) /(in_imfset imfset_key f) /= fx.
    by move=> /(nth_Y2 y yD) /[swap] <-; rewrite inE=> /andP[/negP]. 
  move=> /negP/negP /(nY1_X y yD) yX /negP/negP /(nY1_X x xD) xX.
  by move=> /(in_injf _ _ xX yX). 
Qed.

Lemma fperm_invE f g X : {on f @` X, cancel f & g} -> {in f @` X, cancel g f} ->
  {in f @` X, fperm_inv (mkfperm f X) =1 g}.
Proof. 
  move=> fK gK y /imfsetP[x] /= xX ->.
  rewrite fK ?(in_imfset _ f) //.
  suff->: f x = [fperm x in X => f x] x.
  - by rewrite fperm_invK.
  rewrite mkfpermE //.
  exact/can_in_inj/imfset_can_in/fK. 
Qed.  

End MkFPermTheory. 

End FPerm.
