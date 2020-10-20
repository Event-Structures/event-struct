From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat ssrfun fintype seq.
From Equations Require Import Equations.
From Coq Require Import Relations Program.Basics.
From event_struct Require Import utilities.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section well_founded.

Definition rel_of_fun f : rel nat := [rel a b | f b == some a].

Variable (f : nat ->  seq nat). (* f : nat -> option nat *)
Hypothesis descend : forall a b, a \in (f b) -> a < b. 
(*Hypothesis descend : forall a, if (f a) is some b then b < a else true.*) (* for option nat *)
(*Hypothesis wf_rel : well_founded (rel_of_fun f).*)

(*Lemma closureP a b : 
  reflect (clos_refl_trans_n1 nat (rel_of_fun f) a b) (rt_closure a b).
Proof.
  rewrite /rel_of_fun /rt_closure /pred_of. apply /(iffP idP).
  { funelim (pred_of_aux b [::]).
    { have: pred_of_aux 0 [::] = [::]. done.
      move=>->. done. }
    (*apply: H=> //=.
    apply_funelim (pred_of_aux n.+1 [::]).
    move=> {b} b s H predfb. econstructor. auto. by apply: H.*) admit. }
  funelim (pred_of_aux b [::]).
  admit.
  move=> {b} b s H tr. apply: H. 
Qed.*)

(* Well-founded relation closure definition *)
Equations rt_closure (n : nat) : seq nat by wf n lt :=
  rt_closure n := rt_clos_seq (f n) _
where
  rt_clos_seq (s : seq nat) (m : exists n' p, f n' = p ++ s /\ (n' <= n)) : seq nat :=
  rt_clos_seq (h :: xs) m := rt_closure h ++ rt_clos_seq xs _;
  rt_clos_seq [::] _ := [::].
Next Obligation.
move: (descend h m).
by rewrite H0 mem_cat inE eq_refl orbT=> /(_ isT) /leq_trans/(_ H1) /ltP. Qed.
Next Obligation.
rewrite -cat_rcons in H0; eexists m, _; split=> //; exact: H0. Qed.
Next Obligation.
by exists n, [::]. Qed.

Definition rel_of_closure (a b : nat) : bool := a \in rt_closure b.

(*Equations rt_closure (a b : nat) : bool by wf b :=
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

Lemma add_seq (a : nat) (s : seq nat) : 
  rt_closure_aux a s = rt_closure_aux a [::] ++ s.
Proof.
  generalize a. elim: s=> {a} a; first by rewrite cats0.
  move=> s IHs b.
  apply_funelim (rt_closure_aux a s)=> {a s} a s. 
  apply_funelim (rt_closure_aux a [::]).
  rewrite -Heqcall -Heqcall0. case: (f a).

Lemma rt_sub_lt (a b : nat) : rel_of_closure a b -> a < b.
Proof.
  rewrite /rel_of_closure /rt_closure. funelim (rt_closure_aux b [::]).
  rewrite -Heqcall. case: (f a).
  

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
