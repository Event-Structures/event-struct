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

Definition rel_of_fun (f : nat -> seq nat) : rel nat := [rel a b | a \in f b].

Variable (f : nat ->  seq nat).
Hypothesis descend : forall a b, a \in (f b) -> a < b.

Lemma zero_empty: f 0 = [::].
Proof.
  case H: (f 0)=> [| x s] //=.
  have: x < 0.
  { apply: descend. rewrite H. exact: mem_head. }
  done.
Qed.

Lemma rel_sublt a b : (rel_of_fun f) a b -> a < b.
Proof.
  rewrite/rel_of_fun /=. exact: descend.
Qed.

Lemma nth_in_seq_orbase (x : nat) (s : seq nat) (k : nat) : 
  (nth x s k) \in s \/ (nth x s k = x).
Proof.
  move: x k. elim: s=> //=.
  { move=> x k. have: nth x [::] k = x.
    { by case: k. }
    move=> ->. right. done. }
  move=> x s IHs y k. case: k=> /=.
  { left. exact: mem_head. }
  move=> k. move: (IHs y k)=> [].
  { move=> *. left. rewrite in_cons. apply/orP. by right. }
  move=> *. by right.
Qed.

Lemma nth_in_seq (x : nat) (s : seq nat) (k : nat) : x \in s -> (nth x s k) \in s.
Proof.
  move=> xs. move: (nth_in_seq_orbase x s k)=> [-> | ->] //.
Qed.

(* Well-founded relation closure definition *)
Equations t_closure (n : nat) : seq nat by wf n :=
  t_closure 0 := [::];
  t_closure n.+1 := 
  let fix t_clos_seq (s : seq nat) (k : nat) :=
    if s is _ :: xs then 
      t_closure (nth 0 (f n.+1) k) ++ t_clos_seq xs k.+1
    else [::] in
  (f n.+1) ++ t_clos_seq (f n.+1) 0.
Next Obligation.
  case H: (f n.+1)=> [| x l] /=.
  { rewrite nth_nil. slia. }
  apply/ltP. move: (nth_in_seq_orbase 0 (x :: l) k)=> [].
  { move=> *. apply: descend. by rewrite H. }
  move=> ->. slia.
Qed.

Definition rel_of_closure (a b : nat) : bool := a \in t_closure b.

Lemma rel_of_closure_sublt a b : rel_of_closure a b -> a < b.
Proof.
  rewrite /rel_of_closure. move: a.
  elim/ssrnat.ltn_ind: b. move=> b.
  funelim (t_closure b)=> //=.
  move=> IH a. rewrite mem_cat=> /orP[].
  { move=> *. by apply/descend. }
  move: {1 4}(f n.+1) (subseq_refl (f n.+1)) {2} 0.
  elim=> //=.
  move=> x s IHs xsfn k.
  rewrite mem_cat => /orP[].
  { move: (nth_in_seq_orbase 0 (f n.+1) k)=> [].
    { move=> H1 H2. apply: ltn_trans.
      { apply: IH; last by apply: H2. by apply: descend. }
      by apply: descend. }
    move=> ->. by funelim (t_closure 0). }
  move=> H. apply: IHs.
  { apply/subseq_trans.
    { apply: (subseq_cons s x). }
     done. }
  apply: H.
Qed.

Lemma clos_trans_sublt a b : clos_trans_n1 nat (rel_of_fun f) a b -> a < b.
Proof.
  rewrite/rel_of_fun /=.
  elim; first by apply: descend.
  move=> x y xfy acx ax.
  apply: ltn_trans; first by apply: ax.
  by apply: descend.
Qed. 

(* Well-founded relations properties *)
Lemma closureP a b : 
  reflect (clos_trans_n1 nat (rel_of_fun f) a b) (rel_of_closure a b).
Proof.
  rewrite /rel_of_closure.
  move: a.
  elim/ssrnat.ltn_ind: b => b.
  funelim (t_closure b)=> //= IH a.
  { apply /(iffP idP)=> //=.
    move=> a0. by move: (clos_trans_sublt a0). }
  apply /(iffP idP).
  { rewrite mem_cat=> /orP[].
    { move=> afn. by constructor. }
    move: {1 4}(f n.+1) (subseq_refl (f n.+1)) {2} 0.
    elim=> //= x s IHs xsfn k.
    rewrite mem_cat=> /orP[].
    { move: (nth_in_seq_orbase 0 (f n.+1) k)=> [].
      { move=> H1 H2. apply/clos_trans_tn1/t_trans.
        { have: (nth 0 (f n.+1) k) < n.+1.
          { by apply/descend. }
          move=> nfkn. apply/clos_tn1_trans.
          exact: (IH (nth 0 (f n.+1) k) nfkn a H2). }
        apply/clos_tn1_trans. by constructor. }
      move=> ->. by funelim (t_closure 0). }
    move=> H. apply: IHs.
    { apply/subseq_trans.
      { apply: (subseq_cons s x). }
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
  have: b < c.
  { exact: descend. }
  move=> bc.
  have: a \in t_closure b.
  { by apply/(IH b bc a). }
  move=> atb. right.
  move: {1 3 4 5}(f c) (subseq_refl (f c)) bfc atb.
  elim=> //=.
  move=> x s IHs xsfc.
  rewrite in_cons=> /orP[/eqP |].
  { move=> <- atb. rewrite mem_cat. apply/orP. by left. }
  move=> bs atb. rewrite mem_cat. apply/orP. right.
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
    apply/eqP. rewrite eqseq_cat=> //=. apply/andP. split. done.
    rewrite IHt=> //=. apply/subseq_trans.
    { apply: (subseq_cons t h). }
    done. }
  move=> H. rewrite -H. apply: IHs=> //.
  apply/subseq_trans.
  { apply: (subseq_cons s x). }
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
  rewrite !in_cons => /orP[/eqP -> //|].
  move=> atb /orP[/eqP <-| btc]; first by rewrite atb.
  apply/orP. right. apply/closureP. apply: clos_trans_tn1.
  apply: t_trans.
  { apply: clos_tn1_trans. apply/closureP. exact: atb. }
  apply: clos_tn1_trans. apply/closureP. exact: btc.
Qed.

Lemma rt_closureP a b :
  reflect (clos_refl_trans_n1 nat (rel_of_fun f) a b) (rt_closure_rel a b).
Proof.
  apply /(iffP idP).
  { rewrite /rt_closure_rel. rewrite in_cons=> /orP[/eqP -> | atb].
    { constructor. }
    move: (closureP a b). rewrite/rel_of_closure => refl.
    move: (refl atb). elim.
    { move=> c afc. apply: rtn1_trans. exact: afc. constructor. }
    move=> c d cfd cac crac. apply: rtn1_trans. exact: cfd. done. }
  move=> cab. rewrite /rt_closure_rel /rt_closure.
  rewrite in_cons. apply/orP.
  elim: cab; first by left.
  move=> c d cfd crac [/eqP ->|].
  { move: cfd. rewrite /rel_of_fun /=. funelim (t_closure d).
    by rewrite zero_empty.
    move=> cfn. right. by rewrite mem_cat cfn. }
  move: (closureP a c)=> refl ac. move: (refl ac)=> cac. right.
  apply /(closureP a d) /clos_trans_tn1 /t_trans.
  { apply /clos_tn1_trans. exact: cac. }
  by constructor.
Qed.

End well_founded.
