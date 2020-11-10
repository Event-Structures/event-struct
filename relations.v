From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat ssrfun fintype seq.
From Equations Require Import Equations.
From Coq Require Import Relations Program.Basics.
From event_struct Require Import utilities.

Set Implicit Arguments.
(*Unset Strict Implicit.*)
Unset Printing Implicit Defensive.
Set Equations Transparent.

Section well_founded.

Definition rel_of_fun (f : nat -> seq nat) : rel nat := 
  [rel a b | a \in [seq x <- f b | x != b]].

Variable (f : nat ->  seq nat).
Hypothesis descend : forall a b, a \in (f b) -> a <= b.

Lemma zero_in x : x \in f 0 -> x = 0.
Proof.
  move=> xf0. move: (descend _ _ xf0). by case: x xf0.
Qed.

Lemma zero_filter_empty: [seq x <- f 0 | x != 0] = [::].
Proof.
  case H: [seq x <- f 0 | x != 0]=> [| x s] //=.
  have: x = 0.
  { apply: zero_in.
    have: x \in [seq x <- f 0 | x != 0].
    { rewrite H. exact: mem_head. }
    rewrite mem_filter=> /andP []. done. }
  move=> x0. rewrite x0 in H.
  have: 0 != 0.
  { move: (mem_head 0 s). rewrite -H mem_filter. done. }
  done.
Qed.

Lemma filter_lt n k : k \in [seq x <- f n | x != n] -> k < n.
Proof.
  rewrite mem_filter=> /andP [] kn /descend. slia.
Qed.

Lemma rel_sublt a b : (rel_of_fun f) a b -> a < b.
Proof.
  rewrite/rel_of_fun /=. exact: filter_lt.
Qed.

(* Well-founded relation closure definition *)
Equations t_closure (n : nat) : seq nat by wf n :=
  t_closure 0 := [::];
  t_closure n.+1 := 
  let fix t_clos_seq (s : seq nat) (k : nat) :=
    if s is _ :: xs then 
      t_closure (nth 0 (filter (fun x => x != n.+1) (f n.+1)) k) ++ t_clos_seq xs k.+1
    else [::] in
    [seq x <- f n.+1 | x != n.+1] ++ t_clos_seq (filter (fun x => x != n.+1) (f n.+1)) 0.
Next Obligation.
  case H: [seq x <- f n.+1 | x != n.+1]=> [| x l] /=.
  { rewrite nth_nil. slia. }
  apply/ltP.
  case: nth_sizeP=> [* | *].
  { apply: filter_lt. by rewrite H. }
  slia.
Qed.

Definition rel_of_closure (a b : nat) : bool := a \in t_closure b.

Lemma rel_of_closure_sublt a b : rel_of_closure a b -> a < b.
Proof.
  rewrite /rel_of_closure.
  elim/ssrnat.ltn_ind: b a=> b IH a.
  funelim (t_closure b)=> //=.
  rewrite mem_cat=> /orP[]; first by apply: filter_lt.
  move: {1 4}[seq x <- f n.+1 | x != n.+1] (subseq_refl [seq x <- f n.+1 | x != n.+1]) {2} 0.
  elim=> //= x s IHs xsfn k.
  rewrite mem_cat => /orP[| H].
  { case: nth_sizeP=> [H1 ? H2 |?].
    { apply: ltn_trans.
      { apply: IH; last by apply: H2. exact: filter_lt. }
        exact: filter_lt. }
    by funelim (t_closure 0). }
  apply: IHs.
  { apply/subseq_trans; first by apply: (subseq_cons s x).
     done. }
  exact: H.
Qed.

Lemma clos_trans_sublt a b : clos_trans_n1 nat (rel_of_fun f) a b -> a < b.
Proof.
  rewrite/rel_of_fun /=.
  elim=> [x | x y xfy acx ax]; first by apply: filter_lt.
  apply: ltn_trans; first by apply: ax.
  exact: filter_lt.
Qed. 

(* Well-founded relations properties *)
Lemma closureP a b : 
  reflect (clos_trans_n1 nat (rel_of_fun f) a b) (rel_of_closure a b).
Proof.
  rewrite /rel_of_closure.
  elim/ssrnat.ltn_ind: b a=> b.
  funelim (t_closure b)=> //= IH a.
  { apply /(iffP idP)=> //= a0.
    exact: (clos_trans_sublt a0). }
  apply /(iffP idP).
  { rewrite mem_cat=> /orP[?|]; first by constructor.
    move: {1 4}[seq x <- f n.+1 | x != n.+1] (subseq_refl [seq x <- f n.+1 | x != n.+1]) {2} 0.
    elim=> //= x s IHs xsfn k.
    rewrite mem_cat=> /orP[].
    { case: nth_sizeP=> [atn | sz].
      { move=> H1 H2. apply/clos_trans_tn1/t_trans.
        { apply/clos_tn1_trans. apply/IH; last by apply: H2. exact: filter_lt. }
        apply/clos_tn1_trans. by constructor. }
      by funelim (t_closure 0). }
    move=> H. apply: IHs.
    { apply/subseq_trans; first by apply: (subseq_cons s x).
      done. }
    exact: H. }
  rewrite mem_cat=> closan. apply/orP.
  move: (clos_tn1_trans _ (fun x x0 : nat => rel_of_fun f x x0) _ _ closan).
  move=> ctnan.
  move: (clos_trans_tn1 _ (fun x x0 : nat => rel_of_fun f x x0) _ _ ctnan)=> ctan.
  move: ctan IH.
  case.
  { rewrite/rel_of_fun /= => x ->. by left. }
  rewrite/rel_of_fun /= => b c bfc ctab IH.
  have: a \in t_closure b.
  { apply/IH; first by apply: filter_lt. done. }
  move=> atb. right.
  move: {1 3 4 5}[seq x <- f c | x != c] (subseq_refl [seq x <- f c | x != c]) bfc atb.
  elim=> //= x s IHs xsfc.
  rewrite in_cons=> /orP[/eqP | bs atb].
  { move=> <- atb. by rewrite mem_cat atb. }
  rewrite mem_cat. apply/orP. right.
  have: forall n,
        (fix t_clos_seq (s0 : seq nat) (k : nat) {struct s0} : seq nat :=
          match s0 with
          | [::] => [::]
          | _ :: xs => t_closure (nth 0 s k) ++ t_clos_seq xs k.+1
          end) s n =
        (fix t_clos_seq (s0 : seq nat) (k : nat) {struct s0} : seq nat :=
          match s0 with
          | [::] => [::]
          | _ :: xs => t_closure (nth 0 (x :: s) k) ++ t_clos_seq xs k.+1
          end) s n.+1.
  { move: {1 4 6}s (subseq_refl s). elim=> //= h t IHt hts k.
    apply/eqP. rewrite eqseq_cat ?eq_refl=> //=.
    rewrite IHt=> //=. apply/subseq_trans; first by apply: (subseq_cons t h).
    done. }
  move=> <-. apply: IHs=> //.
  apply/subseq_trans; first by apply: (subseq_cons s x).
  done.
Qed.

(* reflexive-transitive closure definition *)
Definition rt_closure a := a :: t_closure a.

Definition rt_closure_rel a b := a \in rt_closure b. 

Lemma rt_closure_refl a : rt_closure_rel a a.
Proof.
  rewrite /rt_closure_rel /rt_closure. exact: mem_head.
Qed.

Lemma rt_closure_trans a b c :
  rt_closure_rel a b -> rt_closure_rel b c -> rt_closure_rel a c.
Proof.
  rewrite /rt_closure_rel.
  rewrite !in_cons => /orP[/eqP -> //| atb /orP [ /eqP <-| btc]]; first by rewrite atb.
  apply/orP. right. apply/closureP. apply: clos_trans_tn1. apply: t_trans.
  { apply /clos_tn1_trans /closureP. exact: atb. }
  apply /clos_tn1_trans /closureP. exact: btc.
Qed.

Lemma rt_closureP a b :
  reflect (clos_refl_trans_n1 nat (rel_of_fun f) a b) (rt_closure_rel a b).
Proof.
  apply /(iffP idP).
  { rewrite /rt_closure_rel. rewrite in_cons=> /orP[/eqP -> | atb].
    { constructor. }
    move: (closureP a b). rewrite/rel_of_closure => refl.
    move: (refl atb). elim=> [c afc | c d cfd cac crac].
    { apply: rtn1_trans; first by apply: afc. constructor. }
    apply: rtn1_trans; first by apply: cfd. done. }
  move=> cab. rewrite /rt_closure_rel /rt_closure.
  rewrite in_cons. apply/orP.
  elim: cab => [| c d cfd crac [/eqP -> | ac]]; first by left.
  { right. move: cfd. rewrite /rel_of_fun /=. funelim (t_closure d).
    { by rewrite zero_filter_empty. }
    by rewrite mem_cat=> ->. }
  right. move: (closureP a c)=> refl. move: (refl ac)=> cac.
  apply /(closureP a d) /clos_trans_tn1 /t_trans.
  { apply /clos_tn1_trans. exact: cac. }
  by constructor.
Qed.

End well_founded.
