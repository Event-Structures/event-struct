From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun.
From mathcomp Require Import eqtype choice order seq tuple path zify.
From mathcomp Require Import fintype finfun fingraph finmap.
From mathcomp.tarjan Require Import extra.
From eventstruct Require Import utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.

Section SeqUtils.
Context {T : Type}.
Implicit Types (p : pred T) (r : rel T) (s : seq T) (n : nat).

Lemma behead_rcons x s :
  behead (rcons s x) = if s is [::] then [::] else rcons (behead s) x.
Proof. by case: s. Qed.

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
  move=> /IH ->; lia.
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
    apply/andP; split=> //; first lia.
    by rewrite -ltn_subRL.
  move=> [k [<- /andP[]]].
  rewrite leq_eqVlt=> /orP[/eqP ->|??] //.
  by apply/ltnW/sorted_ltn_nth=> //; apply/andP.
Qed.

End SeqUtils.

Arguments sorted_rcons {T} x.

Section SeqEqUtils.
Context {T : eqType}.
Implicit Types (p : pred T) (r : rel T) (s : seq T) (n : nat).

Lemma eq_mem0 s1 s2 :
  s1 =i s2 -> (s1 == [::]) = (s2 == [::]).
Proof.
  case: s1; case s2=> //= x s eqm; rewrite eqxx; apply/idP/idP.
  - by rewrite /= -(in_nil x) eqm inE eqxx.
  by move: (eqm x); rewrite !inE in_nil eqxx /=.
Qed.

Lemma subseq_anti :
  antisymmetric (@subseq T).
Proof.
  move=> s1 s2 /andP[].
  move=> /size_subseq_leqif /leqifP.
  case: ifP=> [/eqP->|_] //.
  move=> /[swap] /size_subseq.
  by rewrite leqNgt=> /negP.
Qed.

Lemma index_inj s :
  {in s &, injective (index^~ s)}.
Proof. 
  move=> x y; elim s=> [|z {}s] IH //=. 
  case: ifP=> [/eqP->|]; case: ifP=> [/eqP->|] => //. 
  rewrite !inE [z == y]eq_sym [z == x]eq_sym => -> -> /=. 
  move=> ?? []; exact/IH.
Qed.

Lemma mkseq_in_uniq (f : nat -> T) n :
  { in iota 0 n &, injective f } -> uniq (mkseq f n).
Proof. by move/map_inj_in_uniq ->; apply: iota_uniq. Qed.

End SeqEqUtils.

Section Slice.
Context {T : eqType}.
Implicit Types (s : seq T) (n m : nat).

Definition slice n m s :=
  take (m - n) (drop n s).

Lemma size_slice n m s :
  (m <= size s)%N -> size (slice n m s) = m - n.
Proof.
  move=> sz.
  rewrite /slice size_takel //.
  rewrite size_drop; lia.
Qed.

Lemma index_drop s x n :
  (n <= index x s)%N -> index x (drop n s) = index x s - n.
Proof.
  move: s; elim n=> [|{}n IH] s nLe.
  - rewrite drop0 subn0 //=.
  rewrite -addn1 -drop_drop.
  move: nLe; case: s=> [|y {}s] //=.
  case: ifP => // _.
  rewrite drop0 ltnS addn1 subSS=> nLe.
  by rewrite IH.
Qed.

Lemma index_drop_uniq s x n :
  uniq s -> (index x s < n <= size s)%N -> index x (drop n s) = size s - n.
Proof.
  move=> uq /andP[] ixLe nLe.
  rewrite memNindex ?size_drop //.
  case: (x \in s)/idP; last first.
  - move=> /negP; exact/contra/mem_drop.
  move: uq; rewrite -{1 2}[s](cat_take_drop n)=> uq xIn.
  by rewrite -(uniq_catLR uq) // in_take_leq.
Qed.

Lemma in_slice_index n m s x :
  (n <= m <= size s)%N -> uniq s -> x \in (slice n m s) = (n <= index x s < m)%N.
Proof.
  rewrite /slice=> sz.
  rewrite in_take_leq; last first.
  - rewrite size_drop; lia.
  move=> uq; case: (n <= index x s)%N/idP.
  - move=> nLe; rewrite index_drop //; lia.
  move=> /negP; rewrite -ltnNge=> ixLe.
  rewrite index_drop_uniq //; lia.
Qed.

End Slice.

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
  - rewrite Hs size_cat size_rcons Hsz; lia.
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
    move: Hc'; rewrite count_cat -cats1 count_cat /= Hp /= Hc; lia.
  by move=> /ltnSE H; apply/(leq_trans (IH s H)); lia.
Qed.

Lemma count_find_nth (x0 : T) p s n :
  (n < count p s) = (find_nth p s n < size s).
Proof.
  symmetry; case H: (n < count p s).
  - case: (split_count_find_nth x0 H).
    move=> x m i s1 s2 ? <- ?.
    rewrite size_cat size_rcons; lia.
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
  by move=> /orP[/eqP|/orP[]] // /(find_nth_ltn p s); lia.
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

Definition mkmask s n : bitseq :=
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
 * However, because of some technical problems of the section mechanism
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
    move=> /orP[/eqP->|] //; first lia.
    by move: Ha=> /allP /[apply].
  move=> Hk _; move: (IH (ltnW Hks) Hk)=> Hkn.
  apply/(leq_ltn_trans Hkn).
  have Hnth: nth 0 s (size s - k.+1) < nth 0 s (size s - k).
  - apply/sorted_ltn_nth=> //.
    apply/andP; split=> //.
    apply/ltn_sub2l=> //.
    lia.
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
  case: ifP=> [|_]; first lia.
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
  rewrite /Order.lt /=; lia.
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
    + by move=> {}x {}y; move: (valP (f y))=> /[swap] /= <-; lia.
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
    apply/sub_lift_homo=> //=; [lia| ..]; last first.
    + by move=> ?? /=; rewrite ltn_add2l.
    move=> {}x {}y /= /negP; rewrite -leqNgt=> Hyn.
    rewrite -[val (f x)]addn0 -addnS; apply/leq_add.
    - by apply/ltnW; move: (valP (f x)).
   apply/(leq_trans _ Hyn); lia.
  rewrite -tnth_nth tcastE esymK Hnth.
  have ->: cast_ord (size_tuple t) i = Ordinal Hi by exact/val_inj.
  by subst s; rewrite nth_mkseq // sub_liftT // -tnth_nth.
Qed.

End MkMaskMask.
