From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat ssrfun fintype.
From Equations Require Import Equations.
From Coq Require Import Relations.
From event_struct Require Import utilities.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section well_founded.

Definition rel_of_fun f : rel nat := fun a b => a == f b.

Variable (f : nat -> nat). (* f : nat -> option nat *)
Hypothesis descend : forall a, f a < a.
(*Hypothesis wf_rel : well_founded (rel_of_fun f).*)


(* Well-founded relation definition *)
Equations rt_closure (a b : nat) : bool by wf b :=
  rt_closure a b with (a > b) => {
    rt_closure a b true := false;
    rt_closure a b false with (a == b) => {
      rt_closure a b false true := true;
      rt_closure a b false false := rt_closure a (f b)
    }
  }.
Next Obligation.
  apply: ltP. exact: descend.
Qed.

Lemma rt_closure_subleq a b : rt_closure a b -> a <= b.
Proof.
  funelim (rt_closure a b); try slia.
  by rewrite -Heqcall.
Qed.

(* Well-founded relations properties *)
Lemma closureP a b : 
  reflect (clos_refl_trans_n1 nat (rel_of_fun f) a b) (rt_closure a b).
Proof.
  rewrite /rel_of_fun. apply /(iffP idP).
  { funelim (rt_closure a b).
    { by rewrite -Heqcall. }
    { have: a = b. by apply/eqP.
      move=>-> ?. by constructor. }
    rewrite -Heqcall=> afb. move: (H afb).
    move=> IH. by econstructor. }
  elim.
  { funelim (rt_closure a a)=> //; slia. }
  move=> ? {b} b /eqP -> ?. funelim (rt_closure a b)=> //=.
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
Qed.

End well_founded.
