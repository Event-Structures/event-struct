From Coq Require Import Relations.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun.
From mathcomp Require Import eqtype choice order seq tuple path zify.
From mathcomp Require Import fintype finfun fingraph finmap.
From mathcomp Require Import generic_quotient.
From mathcomp.tarjan Require Import extra acyclic kosaraju acyclic_tsorted.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.

(* ************************************************************************** *)
(*     Some automation with hints and tactics                                 *)
(* ************************************************************************** *)

(****** Hints to deal with dummy boolean goals ******)

Lemma orbTb a b : [|| a, true | b].
Proof. by case: a. Qed.

Lemma orbbT a b : [|| a, b | true].
Proof. by rewrite !orbT. Qed.

Lemma orbbbT a b c: [|| a, b, c | true].
Proof. by rewrite !orbT. Qed.

Lemma orbbbbT a b c d: [|| a, b, c, d | true].
Proof. by rewrite !orbT. Qed.

#[export] Hint Resolve orbT orbTb orbbT orbbbT orbbbbT : core.

Lemma and3PP P Q R p q r : reflect P p -> reflect Q q -> reflect R r ->
  reflect [/\ P, Q & R] [&& p, q & r].
Proof. by move=> rP rQ rR; apply: (iffP and3P)=> -[/rP ? /rQ ? /rR ?]. Qed.

Lemma andb_iff (a b c d : bool) :
  (a <-> c) -> (b <-> d) -> (a && b <-> c && d).
Proof. by move=> ??; split=> /andP[??]; apply/andP; split; firstorder. Qed.

Lemma iff_eqP (a b : bool) :
  reflect (a <-> b) (a == b).
Proof.
  apply/(equivP idP); split=> [/eqP->|] //.
  case a; case b=> //; intuition.
Qed.

Lemma forall_iff_eqP {T U : Type} P (p : pred T) x y :
  (forall x, reflect (P x) (p x)) -> (P x <-> P y) -> (p x = p y).
Proof.
  move=> /[dup] /(_ x) /rwP[??] /(_ y) /rwP[??] [??].
  apply: eqP; apply/iff_eqP; intuition.
Qed.

Lemma nmem_subset {T : Type} (p q : pred T) x :
  {subset p <= q} -> x \notin q -> x \notin p.
Proof. by move=> subs; apply/contra=> ?; rewrite subs. Qed.

(* ************************************************************************** *)
(*     Anti-homomorphism (i.e. homomorphism with reversed direction)          *)
(* ************************************************************************** *)

(* TODO: recheck the name (antihomomorphism) in the literature *)

Section AntiHomomorphism.
Context (aT rT : Type) (f : aT -> rT).

Definition antihomomorphism_1 (aP rP : _ -> Prop) := forall x, rP (f x) -> aP x.
Definition antihomomorphism_2 (aR rR : _ -> _ -> Prop) :=
  forall x y, rR (f x) (f y) -> aR x y.

End AntiHomomorphism.

Notation "{ 'ahomo' f : x / a >-> r }" :=
  (antihomomorphism_1 f (fun x => a) (fun x => r))
  (at level 0, f at level 99, x name,
   format "{ 'ahomo'  f  :  x  /  a  >->  r }") : type_scope.

Notation "{ 'ahomo' f : x / a }" :=
  (antihomomorphism_1 f (fun x => a) (fun x => a))
  (at level 0, f at level 99, x name,
   format "{ 'ahomo'  f  :  x  /  a }") : type_scope.

Notation "{ 'ahomo' f : x y / a >-> r }" :=
  (antihomomorphism_2 f (fun x y => a) (fun x y => r))
  (at level 0, f at level 99, x name, y name,
   format "{ 'ahomo'  f  :  x  y  /  a  >->  r }") : type_scope.

Notation "{ 'ahomo' f : x y / a }" :=
  (antihomomorphism_2 f (fun x y => a) (fun x y => a))
  (at level 0, f at level 99, x name, y name,
   format "{ 'ahomo'  f  :  x  y  /  a }") : type_scope.

Notation "{ 'ahomo' f : x y /~ a }" :=
  (antihomomorphism_2 f (fun y x => a) (fun x y => a))
  (at level 0, f at level 99, x name, y name,
   format "{ 'ahomo'  f  :  x  y  /~  a }") : type_scope.


Section AntiHomomorphismTheory.
Context (aT rT : Type) (f : aT -> rT).
Context (aR : rel aT) (rR : rel rT).

Lemma mono2aW :
  {mono f : x y / aR x y >-> rR x y} -> {ahomo f : x y / aR x y >-> rR x y}.
Proof. by move=> hf x y axy; rewrite -hf. Qed.

End AntiHomomorphismTheory.

(* ************************************************************************** *)
(*     Decidable morphisms on finite types                                    *)
(* ************************************************************************** *)

Section FinTypeMorphism.
Context (aT : finType) (rT : eqType) (f : aT -> rT).
Implicit Types (aF : aT -> aT) (rF : rT -> rT).
Implicit Types (aOp : aT -> aT -> aT) (rOp : rT -> rT -> rT).

Lemma morph1P aF rF :
  reflect (morphism_1 f aF rF)
          ([forall x, f (aF x) == rF (f x)]).
Proof. repeat apply/forallPP=> ?; exact/eqP. Qed.

Lemma morph2P aOp rOp :
  reflect (morphism_2 f aOp rOp)
          ([forall x, forall y, f (aOp x y) == rOp (f x) (f y)]).
Proof. repeat apply/forallPP=> ?; exact/eqP. Qed.

End FinTypeMorphism.

Section FinTypeHomomorphism.
Context (aT : finType) (rT : Type) (f : aT -> rT).
Implicit Types (aP : pred aT) (rP : pred rT).
Implicit Types (aR : rel aT) (rR : rel rT).

Lemma homo1P aP rP :
  reflect (homomorphism_1 f aP rP)
          ([forall x, aP x ==> rP (f x)]).
Proof. repeat apply/forallPP=> ?; exact/implyP. Qed.

Lemma homo2P aR rR :
  reflect (homomorphism_2 f aR rR)
          ([forall x, forall y, aR x y ==> rR (f x) (f y)]).
Proof. repeat apply/forallPP=> ?; exact/implyP. Qed.

End FinTypeHomomorphism.

Section FinTypeMonomorphism.
Context (aT : finType) (rT : Type) (sT : eqType) (f : aT -> rT).
Implicit Types (aP : aT -> sT) (rP : rT -> sT).
Implicit Types (aR : aT -> aT -> sT) (rR : rT -> rT -> sT).

Lemma mono1P aP rP :
  reflect (monomorphism_1 f aP rP)
          ([forall x, rP (f x) == aP x]).
Proof. repeat apply/forallPP=> ?; exact/eqP. Qed.

Lemma mono2P aR rR :
  reflect (monomorphism_2 f aR rR)
          ([forall x, forall y, rR (f x) (f y) == aR x y]).
Proof. repeat apply/forallPP=> ?; exact/eqP. Qed.

End FinTypeMonomorphism.

(* ************************************************************************** *)
(*     Morphisms of extensionally equal functions                             *)
(* ************************************************************************** *)

Section MorphismEq.
Context (aT rT : Type) (f : aT -> rT) (g : aT -> rT).
Implicit Types (aF : aT -> aT) (rF : rT -> rT).
Implicit Types (aOp : aT -> aT -> aT) (rOp : rT -> rT -> rT).

Hypothesis (eqf : f =1 g).

Lemma eq_morph1 aF rF :
  (morphism_1 f aF rF) <-> (morphism_1 g aF rF).
Proof. split=> mor x; [rewrite -?eqf | rewrite ?eqf]; exact/mor. Qed.

Lemma eq_morph2 aOp rOp :
  (morphism_2 f aOp rOp) <-> (morphism_2 g aOp rOp).
Proof. split=> mor x y; [rewrite -?eqf | rewrite ?eqf]; exact/mor. Qed.

End MorphismEq.

Section HomomorphismEq.
Context (aT rT : Type) (f : aT -> rT) (g : aT -> rT).
Implicit Types (aP : aT -> Prop) (rP : rT -> Prop).
Implicit Types (aR : rel aT) (rR : rel rT).

Hypothesis (eqf : f =1 g).

Lemma eq_homo1 aP rP :
  (homomorphism_1 f aP rP) <-> (homomorphism_1 g aP rP).
Proof. split=> hom x; [rewrite -?eqf | rewrite ?eqf]; exact/hom. Qed.

Lemma eq_homo2 aR rR :
  (homomorphism_2 f aR rR) <-> (homomorphism_2 g aR rR).
Proof. split=> hom x y; [rewrite -?eqf | rewrite ?eqf]; try exact/hom. Qed.

End HomomorphismEq.

Section MonomorphismEq.
Context (aT rT : Type) (sT : Type) (f : aT -> rT) (g : aT -> rT).
Implicit Types (aP : aT -> sT) (rP : rT -> sT).
Implicit Types (aR : aT -> aT -> sT) (rR : rT -> rT -> sT).

Hypothesis (eqf : f =1 g).

Lemma eq_mono1 aP rP :
  (monomorphism_1 f aP rP) <-> (monomorphism_1 g aP rP).
Proof. split=> mon x; [rewrite -?eqf | rewrite ?eqf]; exact/mon. Qed.

Lemma eq_mono2 aR rR :
  (monomorphism_2 f aR rR) <-> (monomorphism_2 g aR rR).
Proof. split=> mon x y; [rewrite -?eqf | rewrite ?eqf]; exact/mon. Qed.

End MonomorphismEq.

(* ************************************************************************** *)
(*     Restriction of the function to subType                                 *)
(* ************************************************************************** *)

Section RstDef.
Context {T U : Type} {P : pred T} {S : subType P}.
Implicit Types  (f : T -> U).

Definition rst f : S -> U := f \o val.

End RstDef.

Notation "[ 'rst' f 'to' S ]" := (rst f : S -> _)
  (at level 0, f at level 99,
   format "[ 'rst'  f  'to'  S ]") : form_scope.

Notation "[ 'rst' f | P ]" := (rst f : (sig P) -> _)
  (at level 0, f at level 99,
   format "[ 'rst'  f  |  P ]") : form_scope.

Section SubFunTheory.
Context {T U : Type} {P : pred T} {S : subType P}.
Implicit Types  (f : T -> U).

Lemma rst_existsE f (PU : U -> Prop) :
  (exists x, PU ([rst f to S] x)) <-> (exists2 x, P x & PU (f x)).
Proof.
  split=> [[x] pux | [x] px pux].
  - exists (val x)=> //; exact/valP.
  by exists (Sub x px); rewrite /rst /= SubK.
Qed.

End SubFunTheory.

(* Variables (T U : Type) (P : pred T) (f : T -> U). *)
(* Check ([rst f | P]). *)

(* ************************************************************************** *)
(*     Surjective function                                                    *)
(* ************************************************************************** *)

Section Surjective.
Context {rT aT : Type}.
Implicit Types (f : aT -> rT).

Definition surjective f := 
  forall (y : rT), exists x, f x = y.

Lemma bij_surj f :
  bijective f -> surjective f.
Proof. by case=> g Kf Kg y; exists (g y); rewrite Kg. Qed.

End Surjective.

Section SurjectivePreim.
Context {rT : eqType} {aT : choiceType}.
Context (f : aT -> rT).
Hypothesis (surjf : surjective f).

Lemma preim_ofP : 
  forall (x : rT), exists y, f y == x.
Proof. by move=> x; case (surjf x)=> [y] <-; exists y. Qed.

Definition preim_of : rT -> aT := 
  fun y => xchoose (preim_ofP y).

(* TODO: rename? *)
Lemma preim_of_f : 
  cancel preim_of f.
Proof. 
  rewrite /preim_of=> y.
  exact/eqP/(xchooseP (preim_ofP y)).
Qed.

(* TODO: rename? *)
Lemma f_preim_of : 
  injective f -> cancel f preim_of.
Proof. 
  move=> injf x.
  apply/injf=> //; apply/eqP. 
  exact/(xchooseP (preim_ofP (f x))).
Qed.

End SurjectivePreim.

Section SurjectiveTheory.
Context {rT : eqType} {aT : choiceType}.
Implicit Types (f : aT -> rT).

Lemma inj_surj_bij f :
  injective f -> surjective f -> bijective f.
Proof. 
  move=> injf surjf.
  exists (preim_of surjf).
  - exact/f_preim_of.
  exact/preim_of_f.
Qed.

End SurjectiveTheory.

Section SurjectiveRst.
Context {rT aT : Type}.
Implicit Types (f : aT -> rT).
Implicit Types (rP : pred rT) (aP : pred aT).

Lemma surj_rstE rP aP f :
  {in rP, surjective [rst f | aP]} <-> (forall y, rP y -> exists2 x, aP x & f x = y).
Proof. by split=> surjf y py; apply/(rst_existsE f (eq^~ y))/surjf. Qed.

End SurjectiveRst.

(* ************************************************************************** *)
(*     Mapping using proof of membership                                      *)
(* ************************************************************************** *)

Section SeqIn.

Context {T : eqType}.
Implicit Type s : seq T.

Fixpoint seq_in_sub s s' (sub : subseq s' s) : seq {x in s} :=
  (if s' is h :: t then
     fun sub =>
       exist _ h (mem_subseq sub (mem_head h t)) ::
       seq_in_sub (subseq_trans (subseq_cons t h) sub)
   else fun => [::]
  ) sub.

Definition seq_in s : seq {x in s} := seq_in_sub (subseq_refl s).

Lemma val_seq_in_sub s s' (sub : subseq s' s) :
  map val (seq_in_sub sub) = s'.
Proof. by elim: s'=> //= ?? IHs in sub *; rewrite IHs. Qed.

Lemma val_seq_in s :
  map val (seq_in s) = s.
Proof. by rewrite /seq_in val_seq_in_sub. Qed.

Lemma seq_in_subE s s' (sub : subseq s' s) :
  seq_in_sub sub = pmap insub s'.
Proof. by rewrite -[in RHS](@val_seq_in_sub s s') map_pK //; apply: valK. Qed.

Lemma seq_inE s :
  seq_in s = pmap insub s.
Proof. by rewrite /seq_in seq_in_subE. Qed.

Lemma seq_in_mem s x (p : x \in s) :
  exist _ x p \in seq_in s.
Proof. by rewrite seq_inE mem_pmap_sub. Qed.

End SeqIn.

Lemma exists_equiv {T} {A B : T -> Prop} :
  (forall x, A x <-> B x) -> (exists x, A x) <-> (exists x, B x).
Proof. move=> H; split=> [][] x /H ?; by exists x. Qed.

Lemma exists2_equiv {T} {A B C D : T -> Prop} :
  (forall x, A x <-> C x) -> (forall x, B x <-> D x) ->
  (exists2 x, A x & B x) <-> (exists2 x, C x & D x).
Proof. move=> H1 H2; split=> [][] x /H1 ? /H2 ?; by exists x. Qed.

Inductive and6 (P1 P2 P3 P4 P5 P6 : Prop) : Prop :=
  And6 of P1 & P2 & P3 & P4 & P5 & P6.

Notation "[ /\ P1 , P2 , P3 , P4 , P5 & P6 ]" :=
  (and6 P1 P2 P3 P4 P5 P6) : type_scope.

Section ReflectConnectives.

Variable b1 b2 b3 b4 b5 b6 : bool.

Lemma and6P : reflect [/\ b1, b2, b3, b4, b5 & b6] [&& b1, b2, b3, b4, b5 & b6].
Proof.
  by case: b1; case: b2; case: b3; case: b4; case: b5; case: b6;
    constructor; try by case.
Qed.

End ReflectConnectives.

Section Swap.
Context {T : eqType}.
Implicit Types (f : T -> T).

Definition swap f x y := fun z =>
  if z == x then f y
  else if z == y then f x
  else f z.

Lemma swap1 f x y : swap f x y x = f y.
Proof. by rewrite /swap eqxx. Qed.

Lemma swap2 f x y : swap f x y y = f x.
Proof. by rewrite /swap eqxx; case: ifP=> // /eqP->. Qed.

Lemma swapNE f x y z : z != x -> z != y -> swap f x y z = f z.
Proof. by rewrite /swap=> /negbTE->/negbTE->. Qed.

Lemma swapxx f x : swap f x x =1 f.
Proof. by move=> y; rewrite /swap eq_sym; case: (x =P y)=> [->|]. Qed.

Lemma swap_inv x y : involutive (swap id x y).
Proof.
  move=> ?; rewrite {2}/swap; case: ifP=> [/eqP->|]; first exact/swap2.
  move/negbT=> ?; case: ifP=> [/eqP->|/negbT ?]; first exact/swap1.
  exact/swapNE.
Qed.

Lemma bij_swap x y f : bijective f -> bijective (swap f x y).
Proof.
  move=> /[dup] bi [g c1 c2].
  apply/(@Bijective _ _ _ (swap g (f x) (f y)))=> z; rewrite /swap.
  - case: (z =P x)=> [->|]; rewrite ?eq_refl ?c1 ?bij_eq //.
    - by case: ifP=> // /eqP.
    case: (z =P y)=> [->|]; first by rewrite ?eq_refl.
    by rewrite ?bij_eq // => /eqP/negbTE->/eqP/negbTE->.
  case: (z =P f x)=>[->|]; rewrite ?c1 ?eq_refl; first by case: ifP=>[/eqP->|].
  case: (z =P f y)=>[->|]; rewrite ?eq_refl // -?[g z == _](bij_eq bi) c2.
  by move/eqP/negbTE->=>/eqP/negbTE->.
Qed.

End Swap.

Section NatUtils.
Implicit Types (n m : nat).

Lemma ltn_total n m :
  [|| n == m, n < m | m < n].
Proof.
  move: (leq_total n m).
  rewrite [n <= m]leq_eqVlt [m <= n]leq_eqVlt.
  by rewrite orbA orbAC orbC eq_sym !orbA orbb.
Qed.

End NatUtils.

Section OptionUtils.

Context {T rT : Type}.
Implicit Types (f : T -> option rT) (p : pred rT) (r : rel rT).

Definition opreim f p : simpl_pred T :=
  [pred x | match f x with Some x => p x | _ => false end].

Definition orelpre f r : simpl_rel T :=
  [rel x y | match f x, f y with Some x, Some y => r x y | _, _ => false end].

Definition mk_total f (tot : forall x, f x) : T -> rT :=
  fun x => oextract (tot x).

Lemma mk_totalE d f x tot :
  @mk_total f tot x = odflt d (f x).
Proof.
  rewrite /mk_total /odflt /oapp.
  move: (tot x)=> {tot}.
  case: (f x)=> [{}x|] //.
Qed.

Lemma mk_totalK g f tot :
  pcancel g f -> cancel g (@mk_total f tot).
Proof.
  move=> K x; rewrite /mk_total.
  move: (tot (g x))=> {tot}.
  case H: (f (g x))=> [{}y|] //= _.
  apply /esym; move: H; rewrite K.
  exact /Some_inj.
Qed.

Lemma mk_total_inj f tot :
  injective f -> injective (@mk_total f tot).
Proof.
  move=> I x y; rewrite /mk_total.
  move: (tot x) (tot y)=> {tot}.
  case H1: (f x)=> [{}x'|] //= _.
  case H2: (f y)=> [{}y'|] //= _.
  move=> H3; move: H3 H2 H1=> <- <-.
  exact /I.
Qed.

End OptionUtils.


Section TupleUtils.
Context {T : Type}.

Lemma eq_from_tuple {s1 s2 : seq T} (eq_sz : size s1 = size s2) :
  tcast eq_sz (in_tuple s1) = in_tuple s2 -> s1 = s2.
Proof.
  have: s2 = val (in_tuple s2) by done.
  move=> /[swap] + ->; move=> <-.
  by rewrite /val /= val_tcast.
Qed.

End TupleUtils.

Section CountableUtils.
Context {T : countType}.

Lemma pickle_inj : injective (@choice.pickle T).
Proof. apply /pcan_inj /choice.pickleK. Qed.

End CountableUtils.


Section FoldUtils.

Lemma foldl_maxn_leq n m s :
  n <= m -> foldl maxn n s <= foldl maxn m s.
Proof.
  move: n m; elim s=> [|k {}s IH n m] => //=.
  rewrite {2 4}/maxn; case: ifP; case: ifP=> //; last 1 first.
  - by move=> ?? /IH.
  - by move=> /negP /(contra_not_leq id) /IH.
  move=> + /negP /(contra_not_leq id).
  move=> + /leq_trans /[apply].
  lia.
Qed.

Lemma foldl_maxn_leq_init n s :
  n <= foldl maxn n s.
Proof.
  move: n; elim s=> [|m {}s IH n] => //=.
  rewrite {2}/maxn; case: ifP=> //.
  move=> H; apply /leq_trans; last by exact/IH.
  by apply ltnW.
Qed.

Lemma foldl_maxn_sorted s :
  sorted (<=%O) s -> foldl maxn 0 s = last 0 s.
Proof.
  elim/last_ind: s=> [|{}s m IH] => //=.
  rewrite foldl_rcons last_rcons {1}/maxn.
  case: ifP=> //=.
  move=> /negP /(contra_not_leq id) + S.
  rewrite IH; last first.
  - apply /(subseq_sorted le_trans (subseq_rcons s m) S).
  rewrite -leEnat le_eqVlt=> /orP[/eqP<-|] //=.
  move: S; rewrite -(@path_min_sorted _ _ 0); last first.
  - apply/allP=> x ?; exact/leq0n.
  rewrite rcons_path=> /andP[] ?.
  by move=> H; rewrite (le_gtF H).
Qed.

End FoldUtils.

Section SeqUtils.
Context {T U : eqType}.
Implicit Types (p : pred T) (r : rel T) (f : T -> U).
Implicit Types (x : T) (s : seq T).

Lemma index_inj s :
  {in s &, injective (index^~ s)}.
Proof. 
  move=> x y; elim s=> [|z {}s] IH //=. 
  case: ifP=> [/eqP->|]; case: ifP=> [/eqP->|] => //. 
  rewrite !inE [z == y]eq_sym [z == x]eq_sym => -> -> /=. 
  move=> ?? []; exact/IH.
Qed.

Lemma map_uniq_inj_in f s : 
  uniq [seq f x | x <- s] -> {in s &, injective f}.
Proof. 
  pose fs := [seq f x | x <- s].
  move=> /uniqP inj_nth x y xin yin.
  rewrite -{1}(@nth_index _ x x s) //. 
  rewrite -{1}(@nth_index _ x y s) //. 
  rewrite -!(nth_map x (f x)) ?index_mem // => nth_eq. 
  apply/(index_inj xin yin)/(inj_nth (f x))=> //=. 
  all: by rewrite size_map inE index_mem. 
Qed.  

(* Lemma mem_map_in f p s x : {in p &, injective f} -> {subset s <= p} -> *)
(*   p x -> (f x \in map f s) = (x \in s). *)
(* Proof. by move=> Hf Hs ?; apply/mapP/idP=> [[y /Hs Hy /Hf->]//|]; exists x. Qed. *)

End SeqUtils.


Notation "@! f" := (fun A => f @` A)%fset
  (at level 10, f at level 8, no associativity, format "@!  f") : fset_scope.

(* Context {T U : choiceType} (f : T -> U) {A : {fset T}}. *)
(* Check (@!f : {fset T} -> {fset U})%fset. *)

Section FSetUtils.
Context {key : unit} {T U : choiceType}.
Implicit Types (p : pred T) (r : rel T) (f : T -> U).
Implicit Types (x : T) (X : {fset T}).

Local Open Scope fset_scope.

Definition fpick X : option T :=
  omap val [pick x : X].

Variant fpick_spec X : option T -> Type :=
  | FPick : forall x : T, x \in X -> fpick_spec X (Some x) 
  | Nofpick : X = fset0 -> fpick_spec X None.

Lemma fpickP X : fpick_spec X (fpick X).
Proof. 
  rewrite /fpick; case: pickP=> /=; first by constructor.
  move=> X0; constructor; apply/fsetP=> x /=; rewrite inE. 
  by apply/idP=> xin; move: (X0 (Sub x xin)).
Qed.

Lemma fpick1 x :
  fpick [fset x] = Some x.
Proof.
  case: fpickP=> [y|] /=.
  - by rewrite inE=> /eqP->.
  by move=> /eqP; rewrite -cardfs_eq0 cardfs1.
Qed.

Lemma in_fset1 (x : T) a :
  (a \in [fset[key] x in [:: x]]) = (a == x).
Proof. by rewrite !mem_imfset //= inE. Qed.

Lemma fset_singl (x : T) :
  [fset[key] x in [:: x]] = [fset x].
Proof. by apply/fsetP=> y; rewrite in_fset1 inE. Qed.

Lemma imfset0 f :
  f @` fset0 = fset0.
Proof. 
  apply/cardfs0_eq/eqP; rewrite -leqn0.
  exact/(leq_trans (leq_imfset_card _ _ _)).
Qed.

Lemma imfset1 f x :
  f @` ([fset x]) = [fset (f x)].
Proof.
  apply/fsetP=> y /=; rewrite !inE.
  apply/idP/idP=> [/imfsetP|].
  - by move=> [] z /=; rewrite inE=> /eqP-> ->.
  move=> /eqP->; apply/imfsetP; exists x=> //=; exact/fset11.
Qed.

Lemma imfsetU f s1 s2 :
  f @` (s1 `|` s2) = (f @` s1) `|` (f @` s2).
Proof.
  apply/fsetP=> x /=; rewrite !inE.
  apply/idP/idP=> [/imfsetP|].
  - move=> [] y /=; rewrite !inE=> + ->.
    by move=> /orP[?|?]; apply/orP; [left|right]; apply/imfsetP; exists y.
  by move=> /orP[|] /imfsetP[] /= y ? ->; apply/imfsetP; exists y=> //;
    rewrite inE; apply/orP; [left|right].
Qed.

Lemma imfset_preim_subs f X :
  {subset X <= preim f (mem (f @` X))}.
Proof. by move=> x xin; rewrite inE /=; apply/imfsetP; exists x. Qed.

Lemma imfset_preim_eq f X :
  injective f -> preim f (mem (f @` X)) =1 (mem X).
Proof.
  move=> finj x /=; apply/idP/idP; last exact/imfset_preim_subs.
  by move=> /imfsetP [y] /= /[swap] /finj ->.
Qed.

Lemma imfset_can_in f g X :
  {on f @` X, cancel f & g} -> {in X, cancel f g}.
Proof. by move=> K x xin; rewrite K ?(in_imfset _ f). Qed.

Lemma inj_in_fsetP f X : 
  reflect {in X &, injective f} (injectiveb [ffun x : X => f (val x)]).
Proof. 
  apply/(equivP (injectiveP _)); split=> injf /= x y; last first.
  - rewrite !ffunE=> eqf; apply/val_inj/injf=> //; exact/valP.
  move=> xin yin eqf.
  have->: x = val (Sub x xin : X) by done.
  have->: y = val (Sub y yin : X) by done.
  by congr val; apply/injf; rewrite !ffunE.
Qed.

Lemma fset_ind (P : {fset T} -> Prop) :
  P fset0 -> (forall x X, x \notin X -> P X -> P (x |` X)) -> forall X, P X.
Proof.
  move=> ? Ps X.
  have [n leMn] := ubnP #|` X|; elim: n => // n IHn in X leMn *.
  case (fset_0Vmem X)=> [->//| [x]/[dup] I /fsetD1K<-].
  apply/Ps/IHn; first by rewrite ?inE eqxx.
  by rewrite (cardfsD1 x) I /= addnC addn1 in leMn.
Qed.

Lemma fset_existsP X p :
  reflect (exists x, x \in X /\ p x) [exists x : X, p (val x)].
Proof.
  apply /equivP; first (by apply /existsP); split.
  - by move=> [] /= [] /= x Hx Px; exists x.
  by move=> [] x [] Hx Px; exists (FSetSub Hx).
Qed.

(* TODO: use `rst s r` (restriction of relation) ? *)
Lemma fset_exists2P X r :
  reflect (exists x y, [/\ x \in X, y \in X & r x y])
          [exists x : X, exists y : X, r (val x) (val y)].
Proof.
  apply /equivP; last split.
  - apply /(@fset_existsP _ (fun x => [exists y, r x (val y)])).
  - by move=> [] x [] Hx /fset_existsP [] y [] Hy Rxy; exists x, y.
  move=> [] x [] y [] Hx Hy Rxy; exists x; split=> //.
  by apply /fset_existsP; exists y.
Qed.

Lemma fset_forallPP X pp p :
  (forall x, reflect (pp x) (p x)) ->
  reflect {in X, forall x, pp x} [forall x : X, p (val x)].
Proof.
  move=> refl; apply /equivP; first (by apply /forallP); split.
  - move=> H x inX; move: (H (Sub x inX)); exact/refl.
  move=> H x; exact/refl/H/(valP x).
Qed.

Lemma fset_forallP X p :
  reflect {in X, forall x, p x} [forall x : X, p (val x)].
Proof. apply/fset_forallPP=> x; exact/idP. Qed.

(* TODO: use `rst s r` (restriction of relation) ? *)
Lemma fset_forall2P X r :
  reflect {in X & X, forall x y, r x y}
          [forall x : X, forall y : X, r (val x) (val y)].
Proof.
  apply /equivP; last split.
  - by apply/(@fset_forallP _ (fun x => [forall y, r x (val y)])).
  - move=> H x y inX inY; move: (H x inX).
    by move=> /forallP=> Hy; move: (Hy (Sub y inY)).
  move=> H x Hx /=; apply/forallP=> y; exact/H.
Qed.

(* Lemma mem_imfset_in (f : T -> U) (p : finmempred T) (P : pred T) :  *)
(*   {in P &, injective f} -> {subset p <= P} -> *)
(*     forall (x : T), x \in P -> (f x \in imfset key f p) = (in_mem x p). *)
(* Proof.  *)
(*   move=> f_inj subs x xin.  *)
(*   rewrite unlock seq_fsetE.  *)
(*   rewrite (mem_map_in f_inj) // => [|y]; rewrite enum_finmemE //.  *)
(*   exact/subs. *)
(* Qed. *)

End FSetUtils.

Section FSetUtilsAux.
Context {key : unit} {T U : choiceType}.
Implicit Types (f : T -> T).
Implicit Types (x : T) (X : {fset T}).

Local Open Scope fset_scope.

Lemma imfset_fsubsE (f : T -> T) X : 
  (X `<=` f @` X) = (f @` X == X).
Proof. 
  apply/idP/idP=> [|/eqP->] //.
  move=> subs; rewrite eq_sym eqEfcard. 
  apply/andP; split=> //; exact/leq_imfset_card.
Qed.

Lemma imfset_fsubs_eq (f : T -> T) X : 
  X `<=` f @` X -> f @` X = X.
Proof. 
  move=> subs; apply/esym/eqP. 
  rewrite eqEfcard; apply/andP; split=> //.
  exact/leq_imfset_card.
Qed.

Lemma fset_inj (f : T -> T) X : 
  f @` X = X -> {in X &, injective f}.
Proof. 
  move=> fX; apply/map_uniq_inj_in.
  rewrite -[uniq _]negbK -ltn_size_undup -leqNgt size_map.
  move: fX; rewrite Imfset.imfsetE -(size_seq_fset imfset_key) => ->.
  exact/leqnn.
Qed.

(* TODO: also prove bijectivity!  *)

(* Definition fset_inv x0 (f : T -> T) X y := *)
(*   odflt x0 (fpick [fset x in X | f x == y]). *)

(* Lemma fset_invK x0 (f : T -> T) X : f @` X = X -> *)
(*   {on X, cancel f & (fset_inv x0 f X)}. *)
(* Proof. *)
(*   move=> /[dup] fX /fset_inj injf x fxin.  *)
(*   rewrite /fset_inv; case: fpickP=> //=. *)
(*   - move=> y; rewrite inE //= => /andP[] /= yin /eqP. *)
(*     move=> /(fset_inj fX); apply=> //. *)
(*     move: fxin; rewrite -{1}fX (mem_imfset_in injf) //. *)
(*   admit. *)
(* Admitted. *)

End FSetUtilsAux.


Section FinTypeUtils.
Context {T U : finType}.
Implicit Types (r : rel T) (f : T -> U).

Lemma inj_inj_bij f (g : U -> T) :
  injective f -> injective g -> bijective f.
Proof. move=> + /leq_card; exact/inj_card_bij. Qed.

Definition bijectiveb f :=
  injectiveb f && (#|U| <= #|T|)%N.

Lemma bijectiveP f :
  reflect (bijective f) (bijectiveb f).
Proof.
  apply/(equivP idP); split; rewrite /bijectiveb.
  - move=> /andP[/injectiveP]; exact/inj_card_bij.
  by move=> /[dup] /bij_inj /injectiveP -> /= /bij_eq_card ->.
Qed.

(* TODO: use `forallPP` instead? *)
Lemma forall2P r :
  reflect (forall x y, r x y) [forall x, forall y, r x y].
Proof.
  apply/(equivP forallP); split.
  - by move=> H x y; move: (H x)=> /forallP.
  by move=> H x; apply/forallP.
Qed.

Lemma forall3P (p : T -> T -> T -> bool) :
  reflect (forall x y z, p x y z) [forall x, forall y, forall z, p x y z].
Proof.
  apply/(equivP forallP); split.
  - by move=> H x y z; move: (H x)=> /forall2P.
  by move=> H x; apply/forall2P.
Qed.

End FinTypeUtils.

(* TODO: better name? (h stands for heterogeneous) *)
Section InvFh.
Context {T U : finType}.
Variable (f : T -> U).
Hypothesis (fbij : bijective f).

Lemma injFh_onto y :
  y \in codom f.
Proof.
  apply/(inj_card_onto (bij_inj fbij)).
  by rewrite (bij_eq_card fbij).
Qed.

Definition invFh y := iinv (injFh_onto y).

Lemma invFh_f : cancel f invFh.
Proof. move=> x; apply: iinv_f; exact/bij_inj. Qed.

Lemma f_invFh : cancel invFh f.
Proof. by move=> y; apply: f_iinv. Qed.

Lemma injFh_bij : bijective invFh.
Proof. exists f; [exact/f_invFh | exact/invFh_f]. Qed.

End InvFh.


Section SubTypeUtils.

Context {T : eqType} {U : Type} {P : pred T} {S : subType P}.

Definition sub_down (g : U -> S) (f : U -> T) : U -> S :=
  fun x => insubd (g x) (f x).

Definition sub_lift (g : T -> U) (f : S -> U) : T -> U :=
  fun x => odflt (g x) (omap f (insub x)).

Definition sub_rel_down (r : rel T) : rel S :=
  [rel x y | r (val x) (val y)].

Definition sub_rel_lift (r : rel S) : rel T :=
  [rel x y | match (insub x), (insub y) with
    | Some x, Some y => r x y
    | _, _ => false
    end
  ].

Definition compatible (g : T -> U) (f : S -> U) : Prop :=
  forall x y, g x = f y -> P x.

Lemma sub_inj (x y : T) (px : P x) (py : P y) :
  Sub x px = Sub y py :> S -> x = y.
Proof. by move=> H; move: (SubK S px) (SubK S py)=> <- <-; rewrite H. Qed.

Lemma sub_val (x : S) px :
  Sub (val x) px = x.
Proof. by apply/val_inj; rewrite SubK. Qed.

Lemma sub_downT y g f x :
  P (f x) -> sub_down g f x = insubd y (f x).
Proof. by move=> ?; rewrite /sub_down /insubd insubT //. Qed.

Lemma val_sub_downT g f x :
  P (f x) -> val (sub_down g f x) = f x.
Proof. by rewrite /sub_down val_insubd; case: ifP. Qed.

Lemma sub_downF g f x :
  ~ P (f x) -> sub_down g f x = g x.
Proof. move=> ?; rewrite /sub_down /insubd insubF //; exact/negP. Qed.

Lemma val_sub_downF g f x :
  ~ P (f x) -> val (sub_down g f x) = val (g x).
Proof. by rewrite /sub_down val_insubd; case: ifP. Qed.

Lemma sub_down_inj_inT (g : U -> S) f (pU := fun x => f x \in P) :
  injective f -> { in pU &, injective (sub_down g f) }.
Proof.
  subst pU; move=> Hf x y; rewrite /in_mem /= => Hx Hy.
  by rewrite /sub_down /insubd !insubT /= => /sub_inj/Hf.
Qed.

Lemma sub_down_inj_inF (g : U -> S) f (pU := fun x => f x \notin P) :
  injective g -> { in pU &, injective (sub_down g f) }.
Proof.
  subst pU; move=> Hg x y; rewrite /in_mem /= => /negP Hx /negP Hy.
  rewrite !sub_downF //; exact/Hg.
Qed.

Lemma sub_liftT g f x Px :
  sub_lift g f x = f (Sub x Px).
Proof. by rewrite /sub_lift /insubd insubT /=. Qed.

Lemma sub_liftF g f x :
  ~ P x -> sub_lift g f x = g x.
Proof. move=> ?; rewrite /sub_lift /insubd insubF //=; exact/negP. Qed.

Lemma sub_lift_inj g f :
  compatible g f -> injective g -> injective f -> injective (sub_lift g f).
Proof.
  move=> Hc Hg Hf x y.
  case: (P x)/idP; case: (P y)/idP=> Hx Hy.
  - rewrite !sub_liftT=> /Hf; exact/sub_inj.
  - by rewrite sub_liftT sub_liftF // => /esym /Hc.
  - by rewrite sub_liftF // sub_liftT=> /Hc.
  rewrite !sub_liftF //; exact/Hg.
Qed.

Lemma sub_lift_homo g f (rT : rel T) (rU : rel U) :
  (forall x y, rT x y -> P y -> P x) ->
  (forall x y, ~ P y -> rU (f x) (g y)) ->
  { homo g : x y / rT x y >-> rU x y } ->
  { homo f : x y / rT (val x) (val y) >-> rU x y } ->
  { homo (sub_lift g f) : x y / rT x y >-> rU x y }.
Proof.
  move=> HrT HrU Hg Hf x y.
  case: (P x)/idP; case: (P y)/idP=> Hx Hy.
  - by rewrite !sub_liftT=> ?; apply/Hf; rewrite !SubK.
  - by rewrite sub_liftT sub_liftF // => ?; apply/HrU.
  - by move: Hx=> /[swap] /HrT /[apply].
  rewrite !sub_liftF //; exact/Hg.
Qed.

Lemma sub_rel_lift_val r (x y : S) :
  sub_rel_lift r (val x) (val y) = r x y.
Proof.
  rewrite /sub_rel_lift /= !insubT; try exact/valP.
  by move=> ??; rewrite !sub_val.
Qed.

Lemma sub_rel_lift_fld r :
  subrel (sub_rel_lift r) [rel x y | P x && P y].
Proof.
  rewrite /sub_rel_lift=> ?? /=.
  by repeat case: insubP=> [? ->|] //.
Qed.

Lemma sub_rel_down_liftK r :
  sub_rel_down (sub_rel_lift r) =2 r.
Proof.
  rewrite /sub_rel_lift /sub_rel_down=> x y /=.
  rewrite !insubT; try exact/valP.
  by move=> ??; rewrite !sub_val.
Qed.

Lemma sub_rel_lift_downK r :
  subrel r [rel x y | P x && P y] -> sub_rel_lift (sub_rel_down r) =2 r.
Proof.
  move=> sub x y /=.
  have ->: r x y = [&& r x y, P x & P y].
  - apply/idP/idP=> [|/and3P[]] //=.
    by move=> /[dup] /sub /andP[] -> -> ->.
  rewrite /sub_rel_lift /sub_rel_down /=.
  apply/idP/idP.
  - repeat (case: insubP=> [? -> ->|] //); by move=> ->.
  move=> /and3P[???].
  repeat (case: insubP=> [?? ->|/negP] //).
Qed.

Lemma sub_rel_liftP (r : rel S) x y :
  reflect (exists x' y', [/\ r x' y', val x' = x & val y' = y])
          (sub_rel_lift r x y).
Proof.
  pose rl := sub_rel_lift r.
  pose r' := [rel x y | P x && P y].
  rewrite -/rl.
  have ->: rl x y = [&& rl x y, P x & P y].
  - apply/idP/idP=> [/[dup] + ->|/and3P[]] //.
    by move=> /sub_rel_lift_fld /andP[-> ->].
  apply/(equivP idP); split.
  - move=> /and3P[rxy px py].
    exists (Sub x px), (Sub y py).
    split; rewrite ?SubK //.
    by move: rxy=> /=; rewrite /rl /sub_rel_lift /= !insubT.
  move=> [x' [] y' []] /=.
  move=> + <- <-; move: (valP x') (valP y').
  move=> /[dup] ? -> /[dup] ? ->.
  by rewrite /rl /sub_rel_lift /= !insubT !andbT !sub_val.
Qed.

Lemma sub_rel_lift_antisym r :
  antisymmetric r -> antisymmetric (sub_rel_lift r).
Proof.
  move=> asym x y.
  rewrite /sub_rel_lift /=.
  case: insubP=> // x' ? <-.
  case: insubP=> // y' ? <-.
  by move=> /asym ->.
Qed.

Lemma sub_rel_lift_trans r :
  transitive r -> transitive (sub_rel_lift r).
Proof.
  move=> trans x y z.
  rewrite /sub_rel_lift /=.
  case: insubP=> // y' ??.
  case: insubP=> // x' ??.
  case: insubP=> // z' ??.
  exact/trans.
Qed.

Lemma eq_sub_rel_down r1 r2 :
  r1 =2 r2 -> sub_rel_down r1 =2 sub_rel_down r2.
Proof. by move=> eqr x y; rewrite /sub_rel_down /= eqr. Qed.

Lemma eq_sub_rel_lift r1 r2 :
  r1 =2 r2 -> sub_rel_lift r1 =2 sub_rel_lift r2.
Proof.
  move=> eqr x y; rewrite /sub_rel_lift /=.
  by do 2 case: insubP=> //.
Qed.

End SubTypeUtils.


Module Export SubFinFun.

Section Def.
Context {aT : finType} {rT : Type}.
Implicit Types (f : {ffun aT -> rT}) (P : pred {ffun aT -> rT}).

Structure subFinfun P : Type := SubFinfun {
  apply :> {ffun aT -> rT};
  _     : P apply;
}.

Canonical subFinfun_subType P := Eval hnf in [subType for (@apply P)].

Definition sub_finfun_of (ph : phant (aT -> rT)) P : predArgType :=
  [subType of (subFinfun P)].

(* TODO: invent better rename or notation? *)
Definition SubFinfunOf f P : P f -> sub_finfun_of (Phant (aT -> rT)) P :=
  fun pf => SubFinfun pf.

End Def.

Notation "{ 'ffun' fT '|' P }" := (sub_finfun_of (Phant fT) P)
  (at level 0, format "{ 'ffun'  fT '|' P }") : type_scope.

Section Instances.
Context {aT : finType}.

Definition subFinfun_eqMixin (rT : eqType) (P : pred {ffun aT -> rT}) :=
  Eval hnf in [eqMixin of {ffun aT -> rT | P} by <:].
Canonical subFinfun_eqType (rT : eqType) (P : pred {ffun aT -> rT}) :=
  Eval hnf in EqType {ffun aT -> rT | P} (subFinfun_eqMixin P).

Definition subFinfun_choiceMixin (rT : choiceType) (P : pred {ffun aT -> rT}) :=
  Eval hnf in [choiceMixin of {ffun aT -> rT | P} by <:].
Canonical subFinfun_choiceType (rT : choiceType) (P : pred {ffun aT -> rT}) :=
  Eval hnf in ChoiceType {ffun aT -> rT | P} (subFinfun_choiceMixin P).

Definition subFinfun_countMixin (rT : countType) (P : pred {ffun aT -> rT}) :=
  Eval hnf in [countMixin of {ffun aT -> rT | P} by <:].
Canonical subFinfun_countType (rT : countType) (P : pred {ffun aT -> rT}) :=
  Eval hnf in CountType {ffun aT -> rT | P} (subFinfun_countMixin P).

Canonical subFinfun_subCountType (rT : countType) (P : pred {ffun aT -> rT}) :=
  Eval hnf in [subCountType of {ffun aT -> rT | P}].

Definition subFinfun_finMixin (rT : finType) (P : pred {ffun aT -> rT}) :=
  Eval hnf in [finMixin of {ffun aT -> rT | P} by <:].
Canonical subFinfun_finType (rT : finType) (P : pred {ffun aT -> rT}) :=
  Eval hnf in FinType {ffun aT -> rT | P} (subFinfun_finMixin P).

Canonical subFinfun_subFinType (rT : finType) (P : pred {ffun aT -> rT}) :=
  Eval hnf in [subFinType of {ffun aT -> rT | P}].

End Instances.

End SubFinFun.


Module Export Subsumes.

Section Def.
Context {T : Type}.
Implicit Types (r : rel T) (mp : mem_pred T).

Definition subsumes_mem r mp1 mp2 :=
  forall x, in_mem x mp1 -> exists2 y, in_mem y mp2 & r x y.

End Def.

Notation "{ 'subsumes' A <= B 'by' R }" :=
  (subsumes_mem R (mem A) (mem B))
    (A at level 69, B at level 69) : type_scope.

Notation "{ 'subsumes' A <= B : x y / a }" :=
  (subsumes_mem (fun x y => a) (mem A) (mem B))
    (A at level 69, B at level 69, x at level 0, y at level 0) : type_scope.

Section Theory.
Context {T : Type}.
Implicit Types (P Q S : pred T) (R : rel T).

Lemma subsumes_refl R P :
  reflexive R -> { subsumes P <= P by R }.
Proof. by move=> ? p ?; exists p. Qed.

Lemma subsumes_trans R P Q S : transitive R ->
  {subsumes P <= Q by R} -> {subsumes Q <= S by R} -> {subsumes P <= S by R}.
Proof.
  move=> trans pq_subs qs_subs p.
  move: pq_subs=> /[apply] [[q]].
  move: qs_subs=> /[apply] [[s]].
  move=> ss /[swap].
  move: trans=> /[apply] /[apply].
  by exists s.
Qed.

End Theory.

End Subsumes.

Section IterUtils.
Context {T : Type}.
Implicit Types (f : T -> T).
Implicit Types (r : rel T).

(* TODO: r could be T -> T -> Prop ? *)
Lemma homo_iter r f n :
  { homo f : x y / r x y } -> { homo (iter n f) : x y / r x y }.
Proof.
  elim n=> [|{}n IH] //=.
  - by move=> ? x y /=.
  move=> homo x y /= ?.
  by apply/homo/IH.
Qed.

Lemma iter_mul_eq n m f x :
  iter m f x = x -> iter (n * m) f x = x.
Proof.
  move=> fmx; elim: n=> [|{}n IH] => //=.
  by rewrite mulSnr iterD fmx IH.
Qed.

End IterUtils.

Arguments homo_iter {T} [r] f n.


Section Imfset.
Open Scope fset_scope.

Lemma imfset_comp (K V W : choiceType)
  (f : K -> V) (g : V -> W) (p : {fset K}) :
  (g \o f) @` p = g @` (f @` p).
Proof.
  apply/fsetP=> a; apply/imfsetP/imfsetP=> [[/= x xA ->]|].
    by exists (f x); rewrite // in_imfset.
  by move=> [/= x /imfsetP [/= y yA ->] ->]; exists y.
Qed.

End Imfset.

Section FinMapCount.
Variable (K : countType) (V : countType).
Implicit Types (d : K -> V).

Definition finMap_countMixin := CanCountMixin (@finMap_codeK K V).
Canonical finMap_countType := CountType {fmap K -> V} finMap_countMixin.

Definition fsfun_countMixin d := [countMixin of (fsfun d) by <:].
Canonical fsfun_countType d := CountType (fsfun d) (fsfun_countMixin d).

End FinMapCount.


Section FinMapUtils.
Context {K : choiceType} {V : eqType}.
Implicit Types (A : {fset K}).

Lemma finsupp_fset (A : {fset K}) (f : K -> V) dflt :
  finsupp [fsfun k in A => f k | dflt] = [fset k in A | f k != dflt]%fset.
Proof.
  apply/fsetP=> x.
  rewrite mem_finsupp fsfunE in_fset !inE /=.
  by case: (x \in A)=> //; rewrite eq_refl.
Qed.

Context {P : pred K} {fK : subFinType P}.

Lemma in_fsetval k :
  (k \in [fsetval k' in fK])%fset = (insub k : option fK).
Proof.
  case: insubP=> /=.
  - move=> k' ? <-; apply/idP/idP=> //.
    by apply/imfsetP; exists k'.
  move=> /negP nPe.
  apply/idP/idP=> //; apply/negP.
  move=> /imfsetP[k''] /= ? H; apply/nPe.
  by move: (valP k''); rewrite H.
Qed.

Lemma in_fsetval_seq k (s : seq fK) :
  (k \in [fsetval k' in s])%fset =
    if insub k is Some k' then k' \in s else false.
Proof.
  case: insubP=> /=.
  - move=> k' ? <-; apply/idP/idP=> //.
    + by move=> /imfsetP[k''] /= + /val_inj ->.
    by move=> ?; apply/imfsetP; exists k'.
  move=> /negP nPk; apply/idP/idP=> //.
  apply/negP=> /imfsetP[k''] /= ? H.
  by move: (valP k''); rewrite -H.
Qed.

End FinMapUtils.


Section QuotUtils.
Variables (T : Type) (e : rel T) (Q : eqQuotType e).

Lemma eqquot_eqP (x y : Q) :
  reflect (x = y) (e (repr x) (repr y)).
Proof. by apply/equivP; first exact/eqquotP; rewrite !reprK. Qed.

Lemma eqquot_eqE (x y : Q) :
  (x == y) = (e (repr x) (repr y)).
Proof. exact/eqP/eqquot_eqP. Qed.

Lemma piK (x : T) :
  (repr (\pi_Q x) = x %[mod Q])%qT.
Proof. by rewrite reprK. Qed.

Lemma eqquot_piE (x : Q) (y : T) :
  x == (\pi y)%qT = e (repr x) y.
Proof.
  rewrite eqquot_eqE; apply/etrans.
  - by rewrite -(@eqquotE T e Q) piK.
  by rewrite -(@eqquotE T e Q).
Qed.

Lemma eqquot_piP (x : Q) (y : T) :
  reflect (x = (\pi y)%qT) (e (repr x) y).
Proof. apply/(equivP idP); rewrite -eqquot_piE; symmetry; exact/(rwP eqP). Qed.


End QuotUtils.
