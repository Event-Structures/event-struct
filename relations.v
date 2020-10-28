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

Definition rel_of_fun f : rel nat := [rel a b | f b == some a].

Variable (f : nat ->  seq nat). (* f : nat -> option nat *)
Hypothesis descend : forall a b, a \in (f b) -> a < b. 
(*Hypothesis descend : forall a, if (f a) is some b then b < a else true.*)
(*Hypothesis wf_rel : well_founded (rel_of_fun f).*)

(* Well-founded relation closure definition *)
Equations rt_closure (n : nat) : seq nat by wf n lt :=
  rt_closure 0 := [::];
  rt_closure n.+1 :=
  let fix rt_clos_seq (s : seq nat) :=
    if s is _ :: xs then rt_closure (head 0 (f n.+1)) ++ rt_clos_seq xs
    else [::] in
  n.+1 :: rt_clos_seq (f n.+1).
Next Obligation.
  case H: (f n.+1)=> /=. slia.
  apply/ltP. apply: descend. rewrite H. exact: mem_head.
Qed.

(*Lemma closureel (a b : nat) : a \in rt_closure b -> a \in (f b) \/
  exists c, c \in (f b) -> a \in rt_closure c.
Proof.
  generalize dependent a.
  elim/ssrnat.ltn_ind: b => b.
  funelim (rt_closure b)=> //= IH a.

Definition rel_of_closure (a b : nat) : bool := a \in rt_closure b.

Lemma rel_of_closure_subleq a b : rel_of_closure a b -> a <= b.
Proof.
  rewrite /rel_of_closure.
  generalize dependent a.
  elim/ssrnat.ltn_ind: b.
  move=> b.
  funelim (rt_closure b)=> /=. move=> //=.
  move=> IH a. case H: (f n.+1)=> //=.
  rewrite mem_cat=> /orP[art |].
  { apply: leq_trans.
    { apply: IH; last by apply: art.
      apply: descend. rewrite H. exact: mem_head. }
    apply: ltnW. apply: descend. rewrite H. exact: mem_head. }
   apply: IH.
   admit.
  
Qed.

(* Well-founded relations properties *)
Lemma closureP a b : 
  reflect (clos_refl_trans_n1 nat (rel_of_fun f) a b) (rel_of_closure a b).
Proof.
  rewrite /rel_of_fun /=. apply /(iffP idP).
  { rewrite /rel_of_closure /rt_closure.
   funelim (rt_closure_aux b [::]).
    rewrite -Heqcall. case H: (f a).
    {  } }
    { have: a = b. by apply/eqP.
      move=>-> ?. by constructor. }
    rewrite -Heqcall=> afb. move: (H afb).
    move=> IH. apply: rtn1_trans. 
    { have: flip (frel f) (f b) b.
      { rewrite /flip //=. }
      move=> fl. exact: fl. }
    done. }
  elim.
  { funelim (rt_closure a a)=> //; slia. }
  move=> ? {b} b. rewrite /flip /= => /eqP <- ?. funelim (rt_closure a b)=> //=.
  { move=> rtafb.
    have: a <= (f b).
    { by rewrite rt_closure_subleq. }
    move=> afb.
    have: a < b.
    { have: f b < b. exact: descend.
      slia. }
    slia. }
  by rewrite Heqcall. 
Qed.

Lemma rt_closure_refl a : rt_closure a a.
Proof.
  funelim (rt_closure a a); try slia; done.
Qed.

Lemma rt_closure_trans a b c : rt_closure a b -> rt_closure b c -> rt_closure a c.
Proof.
  move=> rtab rtbc.
  apply/closureP.
  apply: clos_rt_rtn1.
  apply: rt_trans; apply: clos_rtn1_rt.
  { exact: (closureP a b rtab). }
  exact: (closureP b c rtbc).
Qed.*)

End well_founded.
