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
 * https://github.com/math-comp/math-comp/pull/771 is merged 
 *)
Lemma bij_eq_card f : bijective f -> #|T| = #|T'|.
Proof. by move=> [g /can_inj/leq_card + /can_inj/leq_card]; case: ltngtP. Qed.

End FinTypeUtils.


Section SubTypeUtils.

Context {T : eqType} {U : Type} {P : pred T} {S : subType P}.

Definition sub_down (x : S) (f : U -> T) : U -> S := 
  fun y => insubd x (f y).

Definition sub_lift (x : S) (f : S -> U) : T -> U := 
  fun y => f (insubd x y).

Lemma eq_sub_down x f y : 
  P (f y) -> val (sub_down x f y) = f y. 
Proof. by rewrite /sub_down val_insubd=> ->. Qed.

Lemma sub_liftT x f y Py : 
  sub_lift x f y = f (Sub y Py).
Proof. by rewrite /sub_lift /insubd insubT /=. Qed.

Lemma sub_liftF x f y : 
  ~ P y -> sub_lift x f y = f x.
Proof. move=> ?; rewrite /sub_lift /insubd insubF //=; exact/negP. Qed.

Lemma sub_lift_inj x f : 
  injective f -> {in P &, injective (sub_lift x f)}.
Proof. 
  move=> H y z Hy Hz; rewrite !sub_liftT=> /H ?. 
  rewrite -(SubK S Hy) -(SubK S Hz).
  by apply/eqP/val_eqP.  
Qed.

End SubTypeUtils.


Section SeqUtils.

Context {T : Type}. 
Implicit Types (p : pred T) (s : seq T) (n : nat).

Lemma hasNcount p s : 
   ~~ has p s = (count p s == 0).
Proof. by rewrite has_count -leqNgt leqn0. Qed. 

Lemma hasNtake p s : 
   ~~ has p (take (find p s) s).
Proof. by apply/contra; first apply/find_ltn; rewrite ltnn. Qed.
  
Lemma count_take_find p s : 
  count p (take (find p s) s) = 0.
Proof. apply/eqP; rewrite -hasNcount; apply/hasNtake. Qed.

Lemma count_nth x p s :
  count p s = count p ([seq (nth x s) i | i <- iota 0 (size s)]).
Proof. admit. Admitted.

Lemma mkseqS (f : nat -> T) n : 
  mkseq f n.+1 = rcons (mkseq f n) (f n).
Proof. by rewrite /mkseq -addn1 iotaD add0n map_cat cats1. Qed.

Lemma set_nthE x s n y : 
  set_nth x s n y = (rcons (take n s) y) ++ (drop n.+1 s).
Proof. admit. Admitted.

Lemma find_take p s n : 
  has p (take n s) -> find p (take n s) = find p s. 
Proof. admit. Admitted.

  
End SeqUtils.


Section FindNth.

Context {T : Type}. 
Implicit Types (p : pred T) (s : seq T) (n : nat).

(* TODO: rename to avoid collision with find_nth_spec from mathcomp *)
Fixpoint find_nth p s n := 
  match n with 
  | 0    => find p s
  | n.+1 => 
    let i := find_nth p s n in
    (i.+1 + find p (drop i.+1 s))%N
  end.

Variant split_count_find_nth_spec p : seq T -> nat -> nat -> seq T -> seq T -> T -> Type :=
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
  rewrite -cat_rcons; constructor=> //. 
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

Lemma find_nth_leq p s n m : 
  n <= m -> find_nth p s n <= find_nth p s m.
Proof. 
  elim: m=> [|{}m IH]. 
  - by rewrite leqn0=> /eqP ->.
  rewrite leq_eqVlt=> /orP[/eqP->|] //=.
  move=> /ltnSE /IH H; apply/(leq_trans H). 
  rewrite -addn1 -addnA; exact/leq_addr.
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

Lemma find_nth_cat p s1 s2 n : 
  find_nth p (s1 ++ s2) n = 
    if (count p s1 < n) then 
      find_nth p s1 n 
    else 
      size s1 + find_nth p s2 (n - count p s1).
Proof. admit. Admitted.

End FindNth.


Section MaskUtils.

Context {T : Type}.
Implicit Types (s : seq T) (m : bitseq) (n : nat).

(* Fixpoint mkmask (s : seq nat) m : bitseq := *)
(*   match s with *)
(*   | [::]    => m *)
(*   | i :: s' => set_nth false (mkmask s' m) i true *)
(*   end. *)

Fixpoint mkmask f k n : bitseq :=
  (fix mkmask (s : seq nat) m := match s with
    | [::]    => m
    | i :: s' => set_nth false (mkmask s' m) i true
  end) (mkseq f k) (nseq n false).

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

Lemma mkmaskS f k n :
  mkmask f k.+1 n = set_nth false (mkmask f k n) (f k) true.
Proof. admit. Admitted.

Lemma size_mkmask f k n :
  (forall i, i < k -> f i < n) -> size (mkmask f k n) = n.
Proof. 
  elim k=> [|{}k IH] H //.
  - by rewrite size_nseq. 
  rewrite mkmaskS size_set_nth IH.
  - by apply/maxn_idPr/H.
  by move=> ??; apply/H/ltnW.
Qed.

Lemma nth_mkmask f k n i :
  nth false (mkmask f k n) i = (i \in mkseq f k).
Proof. 
  move: n; elim k=> [|{}k IH] n.  
  - by rewrite /mkmask /= nth_nseq inE; case: ifP.
  rewrite mkmaskS nth_set_nth mkseqS mem_rcons in_cons /=. 
  case: ifP=> //. 
Qed.  

Lemma count_set_nth m i :
   ~~ nth false m i -> count id (set_nth false m i true) = 1 + count id m.
Proof. 
  move: i; elim: m=> [|b {}m IH] i /=.
  - by rewrite set_nth_nil addn0 /= => _; elim i.
  elim i=> [|{}i IHi] => /=.
  - by move=> /negbTE ->. 
  move=> /IH ->; ssrnatlia. 
Qed.

Lemma count_mkmask f k n :
   count id (mkmask f k n) = k.
Proof. 
  elim k=> [|{}k IH]. 
  - by rewrite count_nseq. 
  rewrite mkmaskS count_set_nth ?IH //. 
  rewrite nth_mkmask; apply/(nthP 0).
  move=> [i]; rewrite size_mkseq=> H. 
  rewrite nth_mkseq //.    
  admit. 
Admitted.

Lemma find_nth_mkmask f n k i :
  {homo f : x y / x < y } -> injective f -> (forall i, i < k -> f i < n) -> 
    i < k < n -> find_nth id (mkmask f k n) i = f i.
Proof. 
  (* move=> Hf; elim i=> [|{}i IH]. *)
  (* - admit. *)
  (* move=> H /=. rewrite IH; last admit. *)
  
  (* rewrite leq_eqVlt. => /orP[/eqP->|]. *)

  move=> Hf Hfi.
  move: k; elim i=> [|{}i IH] k /=.
  - elim k=> [|{}k IH] Hm; first by rewrite ltn0 andFb.
    admit.
    (* rewrite -IH.  *)

  move=> Hm Hi; rewrite (IH k); last first.
  - by move: Hi=> /andP[] /ltnW -> ->. 
  - by move=> j /Hm.
  move: i Hi Hm IH; elim k=> [|{}k IHk] i Hi Hm IH.  
  - by move: Hi; rewrite ltn0. 
  move: Hi=> /andP[]; rewrite ltnS leq_eqVlt=> /orP[|].
  - admit.
  move=> Hi Hk; rewrite -IHk //; last first.
  - by move=> j Hj; apply/Hm/ltnW. 
  - by apply/andP; split=> //; apply/ltnW. 

  have Hsz: f k <= size (mkmask f k n).
  - rewrite size_mkmask; first by apply/ltnW/Hm.
    by move=> ??; apply/Hm/ltnW.
  apply/eqP; rewrite eqn_add2l; apply/eqP. 
  rewrite mkmaskS set_nthE drop_cat.
  rewrite size_rcons size_takel //.
  rewrite ltnS Hf; last by apply/ltnW.
  have Hik: (f i).+1 < f k.
  - apply/(@leq_ltn_trans (f i.+1)); exact/Hf. 
  rewrite -cats1 drop_cat size_takel ?Hik //.
  rewrite !find_cat has_cat /= orbT.
  rewrite -(@subnKC (f i).+1 (f k)); last first.
  - apply/(@ltn_trans (f i.+1)); exact/Hf.  
  rewrite addnC -take_drop.
  case: ifP; first by apply/find_take.
  move=> /(has_nthP false)=> H; exfalso; apply/H.
  exists (f (i.+1) - (f i).+1).
  - rewrite size_take size_drop size_mkmask; last first.
    + by move=> j Hj; apply/Hm/ltnW. 
    rewrite ?ltn_sub2r //.
    + by apply/Hf. 
    + by apply/(ltn_trans Hik)/Hm.
    by apply/Hm.
  rewrite nth_take ?nth_drop ?subnKC ?nth_mkmask; last first.
  - by apply/(ltn_sub2r Hik)/Hf.
  - by apply/Hf. 
  by rewrite /mkseq mem_map ?mem_iota ?add0n.
Admitted.

Lemma mkmask_mask (x : T) (n m : nat) (t : (n.+1).-tuple T) (u : m.-tuple T) (f : 'I_n.+1 -> 'I_m) :
  {homo f : x y / x < y} -> injective f ->
  (forall i, f i < m) ->
  (forall i, tnth t i = tnth u (f i)) -> 
    mask (mkmask (sub_lift ord_max f) n.+1 m) u = t.
Proof. 
  move=> Hfh Hf Hm Hn.
  have Hsz: size (mask (mkmask (sub_lift ord_max f) n.+1 m) u) = size t.
  - by rewrite size_mask ?size_mkmask ?count_mkmask ?size_tuple.
  apply/(@eq_from_nth T x)=> //; rewrite Hsz size_tuple=> i Hi.
  pose I := Ordinal Hi; move: (Hn I).
  rewrite !(tnth_nth x)=> ->. 
  rewrite nth_mask ?find_nth_mkmask ?sub_liftT //.  
  - admit. 
  - admit. 
  by rewrite size_mkmask ?size_tuple.
Admitted.

End MaskUtils.


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
