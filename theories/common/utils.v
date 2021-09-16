From Coq Require Import Relations.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun eqtype choice.
From mathcomp Require Import order seq tuple path fintype finmap.
From eventstruct Require Import ssrnatlia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.

(* ************************************************************************** *)
(*     Some automation with hints and tactics                                 *)
(* ************************************************************************** *)

(***** Intro pattern ltac views *****)
(* This is due to Cyril Cohen.
   TODO: remove when https://github.com/math-comp/math-comp/pull/501 is merged *)

Module Export ipat.

Notation "'[' '1' '!' rules ']'"     := (ltac:(rewrite rules))
  (at level 0, rules at level 200, only parsing) : ssripat_scope.
Notation "'[' '!' rules ']'"         := (ltac:(rewrite !rules))
  (at level 0, rules at level 200, only parsing) : ssripat_scope.
Notation "'[' '-!' rules ']'"         := (ltac:(rewrite -!rules))
  (at level 0, rules at level 200, only parsing) : ssripat_scope.
End ipat.

(****** Hints to deal with dummy bolean goals ******)

Lemma orbTb a b : [|| a, true | b].
Proof. by case: a. Qed.

Lemma orbbT a b : [|| a, b | true].
Proof. by rewrite !orbT. Qed.

Lemma orbbbT a b c: [|| a, b, c | true].
Proof. by rewrite !orbT. Qed.

Lemma orbbbbT a b c d: [|| a, b, c, d | true].
Proof. by rewrite !orbT. Qed.

Hint Resolve orbT orbTb orbbT orbbbT orbbbbT : core.

(* ************************************************************************** *)
(*     Additional Notations                                                   *)
(* ************************************************************************** *)

(* TODO: move to `inhtype.v`? add scope? *)
Notation "?| T |" := (inhabited T)
  (at level 0, T at level 99, format "?| T |").

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

Section RelationOnSeq.

Lemma rfoldl {A B C D} (r : A -> C -> bool) (r' : B -> D -> bool) 
  (f : A -> B -> A) (f' : C -> D -> C) (bs : seq B) (ds : seq D)
  (ini : A) (ini' : C) : r ini ini' ->
  (forall a b c d, r a c -> r' b d -> r (f a b) (f' c d)) ->
  all2 r' bs ds -> r (foldl f ini bs) (foldl f' ini' ds).
Proof.
  move=> + H.
  elim: bs ini ini' ds=> [??[]//|?? IHbs ?? []//= ??? /andP[*]].
  by apply/IHbs; first exact/H.
Qed.

Lemma rpath {T S} (sf : T -> S -> bool)  (r' : rel S) (y : S)
  (s : seq S) (r : rel T) (t : seq T) (x : T) : sf x y ->
  (forall a b c d, sf a c -> sf b d -> r a b = r' c d) ->
  all2 sf t s -> 
  path r x t = path r' y s.
Proof.
  move=> + H.
  elim: t x y s=> [??[]//|/=> IHt ?? []//=> /H R /andP[/[dup] /IHt IH+/IH]].
  by move/R->=>->.
Qed.

End RelationOnSeq.

Section Swap.

Context {T : eqType}.

Section SwapDef.

Context (f : T -> T) (a b : T).

Definition swap := fun x =>
  if x == a then
    f b
  else if x == b then 
    f a
  else f x.

Lemma swap1: swap a = f b.
Proof. by rewrite /swap eq_refl. Qed.

Lemma swap2: swap b = f a.
Proof. by rewrite /swap eq_refl; case: ifP=> // /eqP->. Qed.

Lemma swap_not_eq x: x != a -> x != b -> f x = swap x.
Proof. by rewrite /swap=> /negbTE->/negbTE->. Qed.

End SwapDef.

Lemma swapxx x f : swap f x x =1 f.
Proof. by move=> y; rewrite /swap eq_sym; case: (x =P y)=> [->|]. Qed.

Lemma swap_inv a b: involutive (swap id a b).
Proof.
  move=> ?; rewrite {2}/swap; case: ifP=> [/eqP->|]; first exact/swap2.
  move/negbT=> ?; case: ifP=> [/eqP->|/negbT ?]; first exact/swap1.
  exact/esym/swap_not_eq.
Qed.


Lemma bij_swap a b f : bijective f -> bijective (swap f a b).
Proof.
  move=> /[dup] bi [g c1 c2].
  apply/(@Bijective _ _ _ (swap g (f a) (f b)))=> x; rewrite /swap.
  - case: (x =P a)=> [->|]; rewrite ?eq_refl ?c1 ?bij_eq //.
    - by case: ifP=> // /eqP.
    case: (x =P b)=> [->|]; first by rewrite ?eq_refl.
    by rewrite ?bij_eq // => /eqP/negbTE->/eqP/negbTE->.
  case: (x =P f a)=>[->|]; rewrite ?c1 ?eq_refl; first by case: ifP=>[/eqP->|].
  case: (x =P f b)=>[->|]; rewrite ?eq_refl // -?[g x == _](bij_eq bi) c2.
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

Section SeqUtils.
Context {T : Type}.
Implicit Types (x : T) (s : seq T).

(* copy-paste of Tauto.ocons *)
Definition ocons o s := 
  match o with 
  | Some x => x :: s
  | None   => s
  end.

Lemma rcons0 x : 
  rcons [::] x = [:: x].
Proof. done. Qed.

Lemma behead_rcons x s :
  behead (rcons s x) = if nilp s then [::] else rcons (behead s) x.
Proof. case: s=> //=. Qed.

End SeqUtils. 

Section TupleUtils.
Context {T : Type}.

Definition tlast n (t : n.+1.-tuple T) : T := tnth t ord_max. 

Lemma thead_head x n (t : n.+1.-tuple T) : thead t = head x t.
Proof. by rewrite /thead (tnth_nth x). Qed.

Lemma tlast_last x n (t : n.+1.-tuple T) : tlast t = last x t.
Proof. by rewrite /tlast (tnth_nth x) -nth_last size_tuple /=. Qed.

Lemma tlast_rcons n (t : n.-tuple T) x : tlast [tuple of rcons t x] = x.
Proof. by rewrite (tlast_last x) last_rcons. Qed.

(* TODO: duplicate of https://github.com/math-comp/math-comp/pull/777 *)
Lemma val_tcast m n (eq_mn : m = n) (t : m.-tuple T) :
  tcast eq_mn t = t :> seq T.
Proof. by case: n / eq_mn. Qed.

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
  by ssrnatlia.
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

Section FSetUtils.

Context {T : choiceType}.
Implicit Types (s : {fset T}) (p : pred T) (r : rel T).

Lemma fset_existsP s p :
  reflect (exists x, x \in s /\ p x) [exists x : s, p (val x)].
Proof.
  apply /equivP; first (by apply /existsP); split.
  - by move=> [] /= [] /= x Hx Px; exists x. 
  by move=> [] x [] Hx Px; exists (FSetSub Hx). 
Qed.  

(* TODO: use `rst s r` (restriction of relation) ? *)
Lemma fset_exists2P s r :
  reflect (exists x y, [/\ x \in s, y \in s & r x y]) 
          [exists x : s, exists y : s, r (val x) (val y)].
Proof.
  apply /equivP; last split. 
  - apply /(@fset_existsP _ (fun x => [exists y, r x (val y)])).
  - by move=> [] x [] Hx /fset_existsP [] y [] Hy Rxy; exists x, y.
  move=> [] x [] y [] Hx Hy Rxy; exists x; split=> //. 
  by apply /fset_existsP; exists y.
Qed.  

End FSetUtils.


Section FinTypeUtils.

Context {T T' : finType}. 
Implicit Types (f : T -> T').

(* TODO: migrate to `mathcomp` once 
 *   https://github.com/math-comp/math-comp/pull/771 is merged 
 *)
Lemma bij_eq_card f : bijective f -> #|T| = #|T'|.
Proof. by move=> [g /can_inj/leq_card + /can_inj/leq_card]; case: ltngtP. Qed.

End FinTypeUtils.


Section SubTypeUtils.

Context {T : eqType} {U : Type} {P : pred T} {S : subType P}.

Definition sub_down (g : U -> S) (f : U -> T) : U -> S := 
  fun x => insubd (g x) (f x).

Definition sub_lift (g : T -> U) (f : S -> U) : T -> U := 
  fun x => odflt (g x) (omap f (insub x)).

Definition compatible (g : T -> U) (f : S -> U) : Prop := 
  forall x y, g x = f y -> P x. 

Lemma sub_inj (x y : T) (px : P x) (py : P y) : 
  Sub x px = Sub y py :> S -> x = y.
Proof. by move=> H; move: (SubK S px) (SubK S py)=> <- <-; rewrite H. Qed.

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

End SubTypeUtils.


Section SeqUtils.

Context {T : Type}. 
Implicit Types (p : pred T) (r : rel T) (s : seq T) (n : nat).

Lemma headNnil x y s : 
  ~~ nilp s -> head y s = head x s.
Proof. by case: s. Qed.

Lemma lastNnil x y s : 
  ~~ nilp s -> last y s = last x s.
Proof. by case: s. Qed.

Lemma hasNcount p s : 
   ~~ has p s = (count p s == 0).
Proof. by rewrite has_count -leqNgt leqn0. Qed. 

Lemma hasNtake p s : 
   ~~ has p (take (find p s) s).
Proof. by apply/contra; first apply/find_ltn; rewrite ltnn. Qed.
  
Lemma count_take_find p s : 
  count p (take (find p s) s) = 0.
Proof. apply/eqP; rewrite -hasNcount; apply/hasNtake. Qed.

Lemma count_set_nth m i :
   ~~ nth false m i -> count id (set_nth false m i true) = 1 + count id m.
Proof. 
  move: i; elim: m=> [|b {}m IH] i /=.
  - by rewrite set_nth_nil addn0 /= => _; elim i.
  elim i=> [|{}i IHi] => /=.
  - by move=> /negbTE ->. 
  move=> /IH ->; ssrnatlia. 
Qed.

Lemma mkseqS (f : nat -> T) n : 
  mkseq f n.+1 = rcons (mkseq f n) (f n).
Proof. by rewrite /mkseq -addn1 iotaD add0n map_cat cats1. Qed.

Lemma set_nthE x s i y : i < size s ->
  set_nth x s i y = (rcons (take i s) y) ++ (drop i.+1 s).
Proof. 
  move=> Hi; apply/(@eq_from_nth _ x).
  - rewrite size_set_nth size_cat size_rcons. 
    rewrite size_drop size_takel ?maxnE //; exact/ltnW.
  move=> j Hj; rewrite nth_set_nth /=.
  rewrite -cats1 -catA !nth_cat size_takel ?nth_drop /=; last exact/ltnW.
  case: (j < i)/idP.
  - move=> /[dup] Hlt; rewrite nth_take //.
    by rewrite ltn_neqAle=> /andP[/negPf->]. 
  move=> /negP; rewrite -leqNgt ltnS leqn0.
  rewrite leq_eqVlt=> /orP[/eqP->|]. 
  - by rewrite subnn eq_refl /=.
  rewrite ?subn_eq0 eq_sym. 
  move=> /[dup]; rewrite {1}ltnNge=> /negPf->. 
  move=> /[dup]; rewrite {1}ltn_neqAle=> /andP[/negPf-> _]. 
  by move=> ?; rewrite -subnDA addn1 subnKC.
Qed.

Lemma find_take p s n : 
  has p (take n s) -> find p (take n s) = find p s. 
Proof. by rewrite -[in find p s](@cat_take_drop n _ s) find_cat=> ->. Qed.

Lemma sorted_rcons x r s y : 
  sorted r (rcons s y) = sorted r s && (nilp s || r (last x s) y).
Proof. case s=> [|??] //=; exact/rcons_path. Qed.

Lemma sorted_subn (s : seq nat) n : 
  sorted ltn s -> all (fun m => n <= m) s -> sorted ltn (map (subn^~ n) s).  
Proof. 
  elim s=> [|i {}s IH] //=.
  rewrite !path_sortedE; try by exact/ltn_trans. 
  move=> /andP[Hi Hs] /andP[Hn Hleq].
  apply/andP; split=> //; last by apply/IH.
  apply/allP=> j /mapP[k + ->] /=. 
  move: Hi=> /allP /[apply] /= Hk.
  apply/ltn_sub2r=> //.
  by apply/(leq_ltn_trans Hn).
Qed.
 
Lemma sorted_ltn_nth (s : seq nat) i j : 
  sorted ltn s -> i < j < size s -> nth 0 s i < nth 0 s j.
Proof.
  move=> Hs /andP[Hij Hsz].
  suff: (nth 0 s i < nth 0 s j)%O by done.
  rewrite lt_sorted_ltn_nth=> //=.
  exact/(ltn_trans Hij).
Qed.  

Lemma sorted_nth_drop_lt (s : seq nat) i j : 
  sorted ltn s -> i.+1 < size s -> j \in drop i.+1 s -> nth 0 s i < j. 
Proof. 
  move=> Hs Hi Hj; apply/leq_trans.
  - by apply/(@sorted_ltn_nth s i i.+1)=> //; apply/andP.
  have: exists k, (nth 0 s k = j) /\ (i.+1 <= k < size s). 
  - move: Hj=> /(nthP 0) [k].
    rewrite size_drop nth_drop=> ??.
    exists (i.+1 + k); split=> //. 
    apply/andP; split=> //; first by ssrnatlia.
    by rewrite -ltn_subRL.    
  move=> [k [<- /andP[]]].
  rewrite leq_eqVlt=> /orP[/eqP ->|??] //. 
  by apply/ltnW/sorted_ltn_nth=> //; apply/andP.  
Qed.  

Lemma subseq_anti {U : eqType} : 
  antisymmetric (@subseq U).
Proof. 
  move=> s1 s2 /andP[].
  move=> /size_subseq_leqif /leqifP. 
  case: ifP=> [/eqP->|_] //.
  move=> /[swap] /size_subseq. 
  by rewrite leqNgt=> /negP. 
Qed.

End SeqUtils.

Arguments sorted_rcons {T} x.

Section FindNth.

Context {T : Type}. 
Implicit Types (p : pred T) (s : seq T) (n : nat).

(* TODO: rename to avoid collision with find_nth_spec from mathcomp? *)
Fixpoint find_nth p s n := 
  match n with 
  | 0    => find p s
  | n.+1 => 
    let i := find_nth p s n in
    (i.+1 + find p (drop i.+1 s))%N
  end.

Variant split_count_find_nth_spec p : 
  seq T -> nat -> nat -> seq T -> seq T -> T -> Type :=
    FindNth x n i s1 s2 of p x & (size s1 = i) & (count p s1 = n) :
      split_count_find_nth_spec p (rcons s1 x ++ s2) n i s1 s2 x.

Lemma split_count_find_nth x0 p s n : n < count p s ->
  let i := find_nth p s n in
  split_count_find_nth_spec p s n i (take i s) (drop i.+1 s) (nth x0 s i).
Proof.
  move: s; elim n=> [|{}n IH] s H /=.
  - case: (split_find_nth x0); first by rewrite has_count.
    move=> x s1 s2 Hp Hh; constructor=> //.
    - rewrite -cats1 !find_cat has_cat /= Hp orbT addn0 /=.
      by move: Hh; case: ifP=> //. 
    by move: Hh; rewrite has_count -leqNgt leqn0=> /eqP.
  move: H=> /[dup] H; case: (IH s); first by apply/ltnW. 
  move: H=> _ x m i s1 s2; clear s.
  pose s := rcons s1 x ++ s2.
  have Hs: s = rcons s1 x ++ s2 by done.
  move=> Hp Hsz Hcs1 Hc; rewrite -Hs.
  have Hs1 : s1 = take i s.
  - rewrite Hs -cats1 !take_cat size_cat Hsz /=. 
    by rewrite ltnn addn1 leqnn subnn take0 cats0. 
  have Hs1' : rcons s1 x = take i.+1 s.
  - by rewrite Hs take_cat size_rcons Hsz ltnn subnn take0 cats0.
  have Hs2 : s2 = drop i.+1 s.
  - by rewrite Hs drop_cat size_rcons Hsz ltnn subnn drop0. 
  have Hcs2 : 0 < count p s2.
  - move: Hc; rewrite -cats1 !count_cat /= addn0 Hcs1 Hp. 
    by rewrite addn1 -{1}[m.+1]addn0 ltn_add2l.
  have Hszf : i.+1 + find p s2 < size s.
  - move: Hcs2; rewrite -has_count has_find.
    by rewrite Hs size_cat size_rcons Hsz ltn_add2l=> ->.
  rewrite -[s in split_count_find_nth_spec p s m.+1]
           (cat_take_drop (i.+1 + find p s2) s).
  rewrite (drop_nth x0 _)=> //.
  rewrite -cat_rcons. constructor=> //. 
  - by rewrite -nth_drop Hs2 nth_find // has_count -Hs2 //. 
  - by rewrite size_take Hszf.
  rewrite takeD take_drop addnC takeD drop_cat size_takel; last first.
  - rewrite Hs size_cat size_rcons Hsz; ssrnatlia.
  rewrite ltnn subnn drop0 count_cat -Hs1' Hs2.  
  by rewrite -cats1 count_cat Hcs1 count_take_find /= Hp !addn0 addn1. 
Qed.  

Lemma count_Nfind_nth (x0 : T) p s n : 
  (count p s <= n) -> (find_nth p s n >= size s).
Proof. 
  move: s; elim n=> [|{}n IH] s /=.  
  - rewrite leqn0=> /eqP H; rewrite hasNfind=> //.      
    by rewrite has_count -leqNgt H.    
  rewrite leq_eqVlt=> /orP[/eqP H|]. 
  - move: H=> /[dup] H; case: (split_count_find_nth x0).
    + by rewrite H. 
    move=> x m i s1 s2 Hp Hsz Hc Hc'.
    rewrite size_cat size_rcons Hsz.
    rewrite leq_add2l leqNgt -has_find has_count -leqNgt.
    move: Hc'; rewrite count_cat -cats1 count_cat /= Hp /= Hc; ssrnatlia.
  by move=> /ltnSE H; apply/(leq_trans (IH s H)); ssrnatlia.
Qed.

Lemma count_find_nth (x0 : T) p s n : 
  (n < count p s) = (find_nth p s n < size s).
Proof.
  symmetry; case H: (n < count p s).
  - case: (split_count_find_nth x0 H).
    move=> x m i s1 s2 ? <- ?.
    rewrite size_cat size_rcons; ssrnatlia.
  apply/negP/negP; rewrite -leqNgt; apply/(count_Nfind_nth x0).
  by move: H=> /negP/negP; rewrite -leqNgt.
Qed.

Lemma find_nth_ltn p s n m :
  n < m -> find_nth p s n < find_nth p s m.
Proof.
  elim: m=> [|{}m IH] // /ltnSE.
  rewrite leq_eqVlt=> /orP[/eqP->|/IH] /=.
  - exact/leq_addr. 
  move=> H; apply/(ltn_trans H); exact/leq_addr. 
Qed.

Lemma find_nth_leq p s n m : 
  n <= m -> find_nth p s n <= find_nth p s m.
Proof.
  rewrite leq_eqVlt=> /orP[/eqP->|] //. 
  by move=> ?; apply/ltnW/find_nth_ltn.
Qed.

Lemma find_nth_inj p s :
  injective (find_nth p s).
Proof. 
  move=> i j; move: (ltn_total i j). 
  by move=> /orP[/eqP|/orP[]] // /(find_nth_ltn p s); ssrnatlia.
Qed.  
  
Lemma find_nth_consT p x xs n :
  p x -> find_nth p (x::xs) n = if n is n'.+1 then 1 + find_nth p xs n' else 0.
Proof. 
  elim n=> [|{}n IH] //=.
  - case: ifP=> ? //=. 
  move=> ?; rewrite IH //=.
  case n=> [|{}n'] //=.
  by rewrite drop0.
Qed.

Lemma find_nth_consF p x xs n :
  ~~ p x -> find_nth p (x::xs) n = 1 + find_nth p xs n.
Proof. 
  elim n=> [|{}n IH] //=.
  - case: ifP=> ? //=. 
  by move=> ?; rewrite IH.
Qed.

End FindNth.


Section MaskUtils.

Context {T : Type}.
Implicit Types (s : seq T) (m : bitseq) (n : nat).

Lemma mask_size_find_nth s n m : 
   size m = size s -> n < size (mask m s) -> find_nth id m n < size m.
Proof. by move=> /size_mask ->; rewrite (count_find_nth false). Qed.

Lemma mask_size_Nfind_nth s n m : 
   size m = size s -> size (mask m s) <= n -> size m <= find_nth id m n.
Proof. by move=> /size_mask ->; exact/(count_Nfind_nth false). Qed.

Lemma nth_mask (x : T) s m n : 
  size m = size s -> nth x (mask m s) n = nth x s (find_nth id m n). 
Proof. 
  move=> Hsz; case: (n < size (mask m s))/idP; last first. 
  - move=> /negP; rewrite -leqNgt.
    move=> /[dup] ? /(mask_size_Nfind_nth Hsz) ?.
    by rewrite !nth_default -?Hsz.
  move=> /[dup] Hn /(mask_size_find_nth Hsz) Hi.
  move: n m Hsz Hn Hi; elim s=> [|y ys IH] n m /=. 
  - by rewrite mask0 /=. 
  case m=> [|b bs] //; rewrite mask_cons /=.
  move=> [] Hsz; rewrite -cat1s !nth_cat. 
  case H: b=> /=; last first.
  - rewrite subn0 !find_nth_consF //.
    move=> /[dup] Hn /(mask_size_find_nth Hsz) Hi ?.
    by rewrite IH. 
  case: ifP.
  - by rewrite ltnS leqn0=> /eqP -> /=. 
  move=> /negP/negP; rewrite -leqNgt. 
  case n=> [|{}n'] //.
  rewrite find_nth_consT //. 
  rewrite add1n !ltnS subn1 -pred_Sn=> _ Hn Hi /=.  
  by apply/IH.     
Qed.

End MaskUtils.


Section MkMask. 
Context {T : Type}.
Implicit Types (s : seq nat) (m : bitseq) (n : nat).

Fixpoint mkmask s n : bitseq :=
  (fix mkmask (s : seq nat) m := match s with
    | [::]    => m
    | i :: s' => set_nth false (mkmask s' m) i true
  end) s (nseq n false).

Lemma mkmask_cons i s n :
  mkmask (i::s) n = set_nth false (mkmask s n) i true.
Proof. by case s. Qed.  

Lemma size_mkmask s n :
  (all (fun i => i < n) s) -> size (mkmask s n) = n.
Proof. 
  elim s=> [|i {}s IH] //.
  - by rewrite size_nseq.
  rewrite mkmask_cons size_set_nth /=. 
  move=> /andP[Hi Ha]; rewrite IH //=.
  exact/maxn_idPr. 
Qed.

Lemma nth_mkmask s n i :
  nth false (mkmask s n) i = (i \in s).
Proof. 
  move: n; elim s=> [|j {}s IH] n.
  - by rewrite /mkmask /= nth_nseq inE; case: ifP.
  rewrite mkmask_cons nth_set_nth in_cons /=. 
  by case: ifP=> //.
Qed.

Lemma count_mkmask s n :
   uniq s -> count id (mkmask s n) = size s.
Proof. 
  move: n; elim s=> [|i {}s IH] n.
  - by rewrite count_nseq.
  rewrite mkmask_cons /= => /andP[Hi Hu]. 
  rewrite count_set_nth ?IH //.
  rewrite nth_mkmask; apply/(nthP 0).
  move=> [j] Hj; move: Hi=> /[swap] <-.
  by rewrite mem_nth.
Qed.

End MkMask.

(* The following lemmas rely on a similar set of assumptions about a sequence s.
 * Putting all of these assumptions in front of each lemma makes it harder 
 * to read the code and grasp the idea.
 * However, because of some techinical problems of the section mechanism 
 * we cannot declare all these assumptions in a single section.
 * It looks like in the case of a single section 
 * the lemmas' arguments (hypothesis) cannot be generalized and 
 * we cannot apply previous lemmas in subsequent lemmas.
 * Thus we pick a middle ground: we put each lemma in a separate section. 
 * Then we can declare all the assumptions as Hypothesis. 
 * It improves readability and preserves the lemma statments generalized enough.
 *)

Section SortedSizeSubn.
Context {T : Type}.
Variables (s : seq nat) (n i : nat).
Hypothesis (Hs : sorted ltn s) (Ha : all (ltn^~ n) s).
Hypothesis (Hsz : i < size s <= n).

Lemma sorted_size_subn : 
  size s - i <= n - (nth 0 s i).
Proof. 
  (* move: s i Hs Ha Hsz; clear s i Hs Ha Hsz. *)
  move: Hsz=> /andP[Hi Hn].
  pose f := fun i => size s - i.
  pose g := fun i => size s - i.
  pose p := fun i => i < size s.
  have K: {in p, cancel f g}.
  - move=> j; subst f g p=> /= ?.
    rewrite subKn //; exact/ltnW.
  rewrite -[i in nth 0 s i]K //. 
  have ->: size s - i = f i by done.
  have: 0 < f i by rewrite subn_gt0.
  have: f i <= size s by exact/leq_subr.
  elim (f i)=> [|k]; subst g=> //=.
  move=> IH Hks.
  case: (0 < k)/idP; last first.
  - move=> /negP; rewrite -leqNgt leqn0=> /eqP-> _.
    rewrite subn1 nth_last ltn_subCr subn0.
    move: (mem_last 0 s); rewrite in_cons. 
    move=> /orP[/eqP->|] //; first by ssrnatlia.
    by move: Ha=> /allP /[apply].
  move=> Hk _; move: (IH (ltnW Hks) Hk)=> Hkn.
  apply/(leq_ltn_trans Hkn). 
  have Hnth: nth 0 s (size s - k.+1) < nth 0 s (size s - k).
  - apply/sorted_ltn_nth=> //.
    apply/andP; split=> //.
    apply/ltn_sub2l=> //.
    ssrnatlia. 
  apply/(ltn_sub2l _ Hnth)/(ltn_trans Hnth). 
  by rewrite -subn_gt0; apply/(leq_trans Hk). 
Qed.    

End SortedSizeSubn.

Section DropMkMaskLt.
Context {T : Type}.
Variables (s : seq nat) (n j : nat).
Hypothesis (Hs : sorted ltn s) (Ha : all (ltn^~ n) s) (Hj : all (ltn j) s).
Hypothesis (Hsz : size s <= n).

Lemma drop_mkmask_lt :
  drop j.+1 (mkmask s n) = mkmask [seq k - j.+1 | k <- s] (n - j.+1).
Proof. 
  move: s Hs Ha Hj Hsz; clear s Hs Ha Hj Hsz.
  elim=> [|i {}s IH].
  - by move=> /= ?? Hn ?; rewrite drop_nseq.
  rewrite map_cons !mkmask_cons /=. 
  rewrite path_sortedE; last exact/ltn_trans. 
  move=> /andP[Ha Hs] /andP[Hi Hlt] /andP[Hj Hjs] Hn.
  rewrite !set_nthE ?drop_cat /=; last first.
  - rewrite size_mkmask //; exact/ltnW.
  - rewrite size_mkmask //. 
    + apply/ltn_sub2r=> //.
      by apply/(leq_ltn_trans Hj). 
    rewrite all_map /preim; apply/allP.
    move=> k Hk /=; rewrite ltn_sub2r //.
    + by apply/(leq_ltn_trans Hj). 
    by move: Hlt Hk=> /allP /[apply].
  rewrite size_rcons size_takel ?ltnS ?Hj; last first.
  - rewrite size_mkmask //; exact/ltnW.
  rewrite -IH //; last first.
  - exact/ltnW.
  rewrite drop_drop -subSn //.
  rewrite take_drop !subnK //; last exact/ltnW. 
  rewrite drop_rcons //.
  rewrite size_takel ?size_mkmask //.  
  by apply/ltnW.
Qed.

End DropMkMaskLt.

Section DropMkMask.
Context {T : Type}.
Variables (s : seq nat) (n i : nat).
Let j : nat := nth 0 s i.
Hypothesis (Hs : sorted ltn s) (Ha : all (ltn^~ n) s).
Hypothesis (Hsz : i < size s <= n).

Lemma drop_mkmask :
  drop j.+1 (mkmask s n) = mkmask [seq k - j.+1 | k <- drop i.+1 s] (n - j.+1).
Proof. 
  subst j; move: s i Hs Ha Hsz; clear s i Hs Ha Hsz. 
  elim=> [|j {}s IH] i //.
  rewrite mkmask_cons /=.
  rewrite path_sortedE; last exact/ltn_trans. 
  move=> /andP[Hjs Hs] /andP[Hj Ha].
  rewrite set_nthE ?drop_cat ?size_rcons ?size_takel ?size_mkmask //; 
    last exact/ltnW. 
  move=> /andP[Hi Hn].
  have: j <= nth 0 (j :: s) i.
  - move: Hi; case i=> [|{}k] //=. 
    rewrite ltnS=> /(mem_nth 0) Hi. 
    move: Hjs=> /allP=> H; move: (H (nth 0 s k) Hi)=> //; exact/ltnW. 
  case: ifP=> [|_]; first ssrnatlia.
  move: Hi; case i=> [|{}k] /=.
  - move=> Hsz _; rewrite subnn !drop0.
    apply/drop_mkmask_lt=> //; last exact/ltnW. 
  rewrite ltnS=> Hi Hjn. 
  rewrite drop_drop subnK ?ltnS ?IH //.
  apply/andP; split=> //; exact/ltnW.  
Qed.

End DropMkMask.

Section FindMkMask.
Context {T : Type}.
Variables (s : seq nat) (n : nat).
Hypothesis (Hs : sorted ltn s) (Ha : all (ltn^~ n) s).
Hypothesis (Hsz : 0 < size s <= n).

Lemma find_mkmask :
  find id (mkmask s n) = nth 0 s 0.
Proof. 
  move: s Hs Ha Hsz; clear s Hs Ha Hsz.
  elim=> [|i {}s IH] Hl //.
  rewrite mkmask_cons /=. 
  move=> /andP[Hi Ha] Hs.
  rewrite set_nthE; last first.
  - by rewrite size_mkmask. 
  rewrite -?cats1 !find_cat has_cat /= orbT.
  case: (size s == 0)/eqP.
  - move=> /size0nil -> /=.
    rewrite take_nseq; last by exact/ltnW. 
    by rewrite has_nseq andbF size_nseq addn0.
  move=> /eqP; rewrite eqn0Ngt=> /negbNE Hs0. 
  case: ifP=> [|_]; last first.
  - by rewrite size_take size_mkmask ?Hi ?addn0.
  move: Hl=> /=; rewrite lt_path_sortedE=> /andP[Hil Hl]. 
  move=> H; exfalso; move: H.
  move=> /[dup] /find_take; rewrite has_find=> ->.
  rewrite size_take size_mkmask ?Hi ?addn0 //.
  rewrite {}IH //; last first.
  - apply/andP; split=> //; exact/ltnW.
  move: Ha Hs Hs0 Hil Hl; case: s=> [|j {}s'] //.  
  move=> /= ??? /andP[] + ??. 
  rewrite /Order.lt /=; ssrnatlia.
Qed.

End FindMkMask.

Section FindNthMkMask.
Context {T : Type}.
Variables (s : seq nat) (n i : nat).
Hypothesis (Hs : sorted ltn s) (Ha : all (ltn^~ n) s).
Hypothesis (Hsz : i < size s <= n).

Lemma find_nth_mkmask :
  find_nth id (mkmask s n) i = nth 0 s i.
Proof. 
  move: i s Hs Ha Hsz; clear s i Hs Ha Hsz.
  elim=> [|{}i IH] s /=.
  - by apply/find_mkmask. 
  move=> Hl Ha /andP[Hi Hs]. 
  rewrite IH=> //; last first.
  - apply/andP; split=> //; exact/ltnW.
  rewrite drop_mkmask ?find_mkmask //; last first.
  - apply/andP; split=> //; exact/ltnW.
  - rewrite size_map size_drop; apply/andP; split.
    + by rewrite subn_gt0.
    rewrite !subnS -subn1 -subn1 leq_sub2r //. 
    apply/sorted_size_subn=> //. 
    apply/andP; split=> //; exact/ltnW.
  - rewrite all_map; apply/allP=> j Hj /=.
    rewrite -subSn; last first.
    + apply/sorted_nth_drop_lt=> //.
    by apply/leq_sub2r/(allP Ha)/mem_drop/Hj.
  - apply/sorted_subn=> //.
    + by apply/drop_sorted.     
    apply/allP=> j Hj.
    by apply/sorted_nth_drop_lt. 
  rewrite (nth_map 0) ?nth_drop ?addn0; last first.
  - by rewrite size_drop subn_gt0.
  rewrite subnKC //.
  suff: (nth 0 s i < nth 0 s i.+1)%O by done.
  apply/nth_count_lt; last by rewrite count_lt_nth. 
  by move: Hl; rewrite lt_sorted_uniq_le=> /andP[].
Qed.

End FindNthMkMask.

Section MkMaskMask.
Context {T : Type} {n m : nat}.
Variables (t : n.-tuple T) (u : m.-tuple T) (f : 'I_n -> 'I_m).
Let s := mkseq (sub_lift (addn m) f) n.

Hypothesis (Hhm  : {homo f : x y / x < y}).
Hypothesis (Hinj : injective f).
Hypothesis (Hnm  : forall i, f i < m).
Hypothesis (Hnth : forall i, tnth t i = tnth u (f i)).

Lemma mkmask_mask :
  mask (mkmask s m) u = t.
Proof. 
  (* move=> Hfh Hf Hm Hn. *)
  have Ha: all (fun i : nat => i < m) s.
  - apply/allP=> i /(nthP 0) [j]. 
    rewrite size_mkseq=> Hj <-.
    by rewrite nth_mkseq // sub_liftT.
  have Hsz: size (mask (mkmask s m) u) = size t.
  - rewrite size_mask ?size_mkmask ?count_mkmask ?size_tuple //.
    apply/mkseq_uniq/sub_lift_inj.
    + by move=> {}x {}y; move: (valP (f y))=> /[swap] /= <-; ssrnatlia.
    + by move=> ??; apply/addnI. 
    by move=> ???; apply/Hinj/val_inj. 
  have Hsz': size (mask (mkmask s m) u) = n.
  - by rewrite Hsz size_tuple.
  apply/(@eq_from_tuple _ _ _ Hsz).
  rewrite tvalK; apply/eq_from_tnth.
  move=> i; rewrite tcastE /tnth /=.
  have Hi: i < n by move: i=> []; rewrite size_tuple.
  rewrite nth_mask ?find_nth_mkmask=> //; last first.
  - by rewrite size_mkmask ?size_tuple //.
  - rewrite size_mkseq; apply/andP; split=> //.
    move: Hinj Hi=> /leq_card /=. 
    by rewrite !card_ord.
  - apply/homo_sorted; last by exact/iota_ltn_sorted.
    apply/sub_lift_homo=> //=; [by ssrnatlia| ..]; last first.
    + by move=> ?? /=; rewrite ltn_add2l.
    move=> {}x {}y /= /negP; rewrite -leqNgt=> Hyn.
    rewrite -[val (f x)]addn0 -addnS; apply/leq_add. 
    - by apply/ltnW; move: (valP (f x)). 
    by apply/(leq_trans _ Hyn); ssrnatlia.
  rewrite -tnth_nth tcastE esymK Hnth. 
  have ->: cast_ord (size_tuple t) i = Ordinal Hi by exact/val_inj.
  by subst s; rewrite nth_mkseq // sub_liftT // -tnth_nth.
Qed.

End MkMaskMask.

(* TODO: move to `inhtype.v` *)
Section InhabitedUtils.

Context {T U : Type}.

(* TODO: use this lemma in lposet.v/thomP proof *)
Lemma nihn_inh_fun : 
  ~ inhabited T -> inhabited (T -> U).
Proof. 
  move=> H; constructor. 
  have fT: (forall x : T, False).
  - move=> x; apply/H; constructor; exact/x. 
  by refine (fun x => match fT x with end).
Qed.

End InhabitedUtils.
