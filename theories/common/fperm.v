From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.
From mathcomp Require Import eqtype choice seq fintype finfun finmap zify.
From eventstruct Require Import utils seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset_scope.
Local Open Scope fmap_scope.

Declare Scope fperm_scope.
Delimit Scope fperm_scope with fperm.

Local Open Scope fperm_scope.

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

Definition fperm0 : fPerm := 
  Sub [fsfun] (introT fsinjectiveP (fsfun0_inj (@inj_id T))).

(* The idea of implementation is due to Arthur Azevedo de Amorim
 * https://github.com/arthuraa/extructures/blob/master/theories/fperm.v
 * TODO: it would be nice to unify mathcomp/finmap & extructures eventually.
 *)
Definition fperm_fun (f : T -> T) X x := 
  let Y1  := (f @` X) `\` X in
  let Y2  := X `\` (f @` X) in
  if x \in Y1 then nth x Y2 (index x Y1) else f x.

Definition fperm_fsfun (f : T -> T) X : {fsfun T -> T} := 
  [fsfun x in X `|` (f @` X) => fperm_fun f X x].

Definition fperm (f : T -> T) X : fPerm :=
  odflt fperm0 (insub (fperm_fsfun f X)).

Definition fperm_swap x y : fPerm :=
  fperm (swap id x y) [fset x; y].

Definition fperm_comp (g f : fPerm) : fPerm := 
  fperm (g \o f) (finsupp g `|` finsupp f).

Definition fperm_inv f :=
  fperm (preim_of (fperm_surj f)) (finsupp f).

End Def.

Module Export Syntax. 

Notation "{ 'fperm' T }" := (@fPerm T) 
  (at level 0, format "{ 'fperm'  T }") : type_scope.

Notation "[ 'fperm' ]" := (fperm0) 
  (at level 0, format "[ 'fperm' ]") : fun_scope.

Notation "[ 'fperm' x \ y ]" := (fperm_swap x y) 
  (at level 0, x at level 99, y at level 99, 
    format "[ 'fperm'  x  \  y ]") : fun_scope.

Notation "[ 'fperm' x 'in' X => F ]" := (fperm (fun x => F) X)
  (at level 0, x at level 99, format "[ 'fperm'  x  'in'  X  =>  F ]") 
  : fun_scope.

Notation "g \o f" := (fperm_comp g f) : fperm_scope.

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
Implicit Types (f g : {fperm T}).
Implicit Types (p : pred T) (X : {fset T}) (x : T).

Lemma fsub_fperm_finsupp (f : T -> T) X : 
  finsupp [fperm x in X => f x] `<=` X `|` f @` X.
Proof. 
  rewrite /fperm; case: insubP => /= [g _ ->|_]. 
  - exact/finsupp_sub. 
  by rewrite finsupp0 fsub0set. 
Qed.

Lemma fperm_fsfunE (f : T -> T) X : {in X &, injective f} -> 
  [fperm x in X => f x] = fperm_fsfun f X :> {fsfun T -> T}.
Proof. 
  move=> in_injf; rewrite /fperm insubT //=. 
  apply/fsinjectiveP/(fsinjP 2 0)=> /=.
  exists (X `|` (f @` X)).
  - exact/finsupp_sub.
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
  - case=> /= x; rewrite /fperm_fsfun /fperm_fun fsfunE.
    move=> /[dup] xD ->; case: ifP.
    + by move=> /(nth_Y2 x xD); rewrite !inE=> /andP[_ ->].
    by move=> /negP/negP/(nY1_X x xD) ?; rewrite inE (in_imfset _ f).
  move=> x y xD yD; rewrite /fperm_fsfun /fperm_fun !fsfunE xD yD.
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

Lemma fperm_inE (f : T -> T) X : {in X &, injective f} -> 
  {in X, [fperm x in X => f x] =1 f}.
Proof. 
  move=> in_injf x xin; rewrite fperm_fsfunE //.
  by rewrite fsfunE /fperm_fun !inE xin.
Qed.

Lemma fpermE (f : T -> T) X : f @` X = X -> 
  forall x, [fperm x in X => f x] x = if x \in X then f x else x.
Proof.
  move=> fX x.
  have injf: {in X &, injective f} by exact/fset_inj. 
  case: ifP=> [?|]; first by rewrite fperm_inE.
  by rewrite fperm_fsfunE // fsfunE fX fsetUid=> ->.
Qed.    

Lemma fperm_imfsetE f X : 
  finsupp f `<=` X -> f @` X = X.
Proof. 
  move=> subs; apply/eqP; rewrite -imfset_fsubsE. 
  apply/fsubsetP=> x xin. 
  case: (x \in finsupp f)/idP=> [insup | /negP]; last first.
  - move=> /fsfun_dflt <-; exact/in_imfset. 
  have K: cancel (preim_of (fperm_surj f)) f.
  - exact/preim_of_f.
  rewrite -[x]K mem_imfset /=; last exact/fperm_inj.
  apply/(fsubsetP subs); move: insup. 
  rewrite !mem_finsupp K.
  by apply/contra=> /eqP {1}->; rewrite K.
Qed.

(* TODO: move to utils.v, also rename it? *)
Lemma swap_imfsetE x y : 
  swap id x y @` [fset x; y] = [fset x; y].
Proof. 
  apply/fsetP=> {}z.
  rewrite -[z in LHS](swap_inv x y) mem_imfset /=; last first.
  - by apply/bij_inj/bij_swap; exists id.
  rewrite !inE /swap. 
  case: (z =P x); rewrite ?eqxx ?orbT //=.
  case: (z =P y); rewrite ?eqxx ?orbT //=.
  by move=> /eqP /negPf -> /eqP /negPf ->.
Qed.
  
Lemma fperm_swapE x y : 
  [fperm x \ y] =1 swap id x y.
Proof. 
  move=> z; rewrite fpermE ?inE ?swap_imfsetE //. 
  case: (z =P x)=> [->|] /=; rewrite ?swap1 //.
  case: (z =P y)=> [->|] /=; rewrite ?swap2 //.
  move=> /eqP ? /eqP ?; exact/esym/swapNE. 
Qed.  

Lemma fperm_compE f g : 
  (g \o f)%fperm =1 (g \o f)%FUN.
Proof. 
  move=> x /=; rewrite /fperm_comp fpermE.
  - rewrite inE; case: ifP=> // /negP/negP.
    rewrite negb_or=> /andP[nf ng].
    by rewrite (fsfun_dflt ng) (fsfun_dflt nf).
  rewrite imfset_comp [f @` _]fperm_imfsetE ?fperm_imfsetE //.
  - exact/fsubsetUl.
  rewrite fsetUC; exact/fsubsetUl.
Qed.

Lemma fperm_invE f :
  fperm_inv f =1 preim_of (fperm_surj f).
Proof. 
  have K: cancel f (preim_of (fperm_surj f)).
  - exact/f_preim_of/fperm_inj.
  have K': cancel (preim_of (fperm_surj f)) f.
  - exact/preim_of_f.
  move=> x; rewrite fpermE; first case: ifP=> //.
  - by rewrite mem_finsupp=> /negP/negP/eqP {2}<-; rewrite K.
  apply/fsetP=> {}x.
  rewrite -[x in LHS]K mem_imfset ?mem_finsupp //=; last first.
  - exact/can_inj/K'. 
  suff: (f (f x) == f x) = (f x == x) by move=> ->.
  apply/idP/idP=> [|/eqP {1}->] //.
  move=> /eqP=> eqfx; apply/eqP.
  by rewrite -[x in RHS]K -[f x in RHS]eqfx K. 
Qed.

Lemma fperm_invK f : cancel f (fperm_inv f).
Proof. 
  apply/(eq_can _ (frefl f) (fsym (fperm_invE f))).
  exact/f_preim_of/fperm_inj. 
Qed.

Lemma inv_fpermK f : cancel (fperm_inv f) f.
Proof. 
  apply/(eq_can _ (fsym (fperm_invE f)) (frefl f)).
  exact/preim_of_f. 
Qed.

Lemma fperm_inv_inj f : injective (fperm_inv f).
Proof. exact/can_inj/inv_fpermK. Qed.

Lemma fperm_inv_mem_finsupp f x :
  (fperm_inv f x \in finsupp f) = (x \in finsupp f).
Proof.
  rewrite !mem_finsupp inv_fpermK.
  suff: (x == fperm_inv f x) = (f x == x) by move=> ->.  
  apply/idP/idP=> /eqP eqx; apply/eqP.
  - by rewrite eqx inv_fpermK.
  by rewrite -eqx fperm_invK.
Qed.

Lemma fperm_inv_can_onE (f g : T -> T) X : {on f @` X, cancel f & g} -> 
  {in f @` X, cancel g f} -> {in f @` X, fperm_inv [fperm x in X => f x] =1 g}.
Proof. 
  move=> fK gK y /imfsetP[x] /= xX ->.
  rewrite fK ?(in_imfset _ f) //.
  suff->: f x = [fperm x in X => f x] x.
  - by rewrite fperm_invK.
  rewrite fperm_inE //. 
  exact/can_in_inj/imfset_can_in/fK. 
Qed. 

Lemma fperm_inv_canE (f g : T -> T) X : f @` X = X -> cancel f g -> cancel g f ->
  forall x, fperm_inv [fperm x in X => f x] x = if x \in X then g x else x. 
Proof.
  move=> fX K K' x.
  case: ifP=> [?|]; first by rewrite (@fperm_inv_can_onE f g) // fX.
  move=> /negP/negP xn; rewrite fperm_invE.
  suff eqx: x = [fperm x in X => f x] x.
  - rewrite [in LHS]eqx f_preim_of //; exact/fperm_inj.
  have xnfx: x \notin X `|` f @` X.
  - by rewrite fX inE negb_or xn. 
  rewrite fsfun_dflt //; apply/nmem_subset; last exact/xnfx.
  exact/fsubsetP/fsub_fperm_finsupp.
Qed.

Lemma fperm_swap_invE x y : 
  fperm_inv [fperm x \ y] = [fperm x \ y].
Proof. 
  apply/val_inj/fsfunP=> z /=; rewrite fperm_swapE. 
  rewrite (@fperm_inv_canE _ (swap id x y)); try exact/swap_inv; last first.
  - by rewrite swap_imfsetE.
  case: ifP=> //; rewrite !inE=> /negP/negP.
  by rewrite negb_or /swap=> /andP[] /negPf -> /negPf ->.
Qed.

Lemma fperm_comp_invE f g : 
  fperm_inv (g \o f)%fperm = (fperm_inv f \o fperm_inv g)%fperm.
Proof. 
  apply/val_inj/fsfunP=> x /=.
  rewrite fperm_compE /= !fperm_invE.
  repeat (apply/canRL; first exact/f_preim_of/fperm_inj).
  rewrite -[x in RHS](preim_of_f (fperm_surj (g \o f))).
  by rewrite fperm_compE.
Qed.  

End Theory. 

End FPerm.
