From Coq Require Import Lia.
From Coq Require Import Relations Relation_Operators Program.Basics.
From mathcomp Require Import ssreflect ssrbool eqtype ssrfun seq order.
From Equations Require Import Equations.
From event_struct Require Import utilities wftype.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Set Equations Transparent.

Import Order.LTheory.
Local Open Scope order_scope.

Section well_founded.

Definition sfrel {T : eqType} (f : T -> seq T) : rel T :=
  [rel a b | a \in f b].

Definition filter_neq {T : eqType} (f : T -> seq T) : T -> seq T :=
  fun n => filter^~ (f n) (fun x => x != n).

Notation "f '\eq'" := (filter_neq f) (at level 5, format "f '\eq'").

Context {disp : unit} {T : wfType disp}.

Variable (f : T -> seq T).

Hypothesis descend : forall x n, x \in f n -> x <= n.

Lemma filter_lt n k : k \in f\eq n -> k < n.
Proof. by rewrite mem_filter lt_neqAle => /andP[] -> /descend ->. Qed.

Lemma rel_sublt a b : (sfrel f\eq) a b -> a < b.
Proof. rewrite/sfrel /=. exact: filter_lt. Qed.

Definition hack n (g : forall x : T, x < n -> seq T) := 
  let ys := f\eq n in 
  let ps := flatten (map^~ ys (fun x => 
  if x \in ys =P true is ReflectT pf then
    g x (filter_lt _ _ pf)
  else
    [::]
)) in ys ++ ps.

Arguments hack /.

(* Computation of the strict upward set of a given element
 * w.r.t relation R derived from function `f`,
 * i.e. s_up_set(x) = { y | x R y } 
 *)
Equations s_up_set (n : T) : seq T by wf n (<%O : rel T) :=
  s_up_set n := hack n s_up_set.

Definition t_closure (a b : T) : bool := a \in s_up_set b.

Lemma clos_trans_lt a b : clos_trans_n1 T (sfrel f\eq) a b -> a < b.
Proof.
  rewrite/sfrel /=.
  elim=> [x /filter_lt // | x y xfy acx ax].
  apply: lt_trans; first exact: ax.
  exact: filter_lt.
Qed.

Notation step := (@tn1_trans T (sfrel f\eq) _ _ _).
Notation base := (@tn1_step T (sfrel f\eq) _).

(* Transitive closure reflection lemma *)
Lemma t_closureP a b : 
  reflect (clos_trans_n1 T (sfrel f\eq) a b) (t_closure a b).
Proof.
  rewrite /t_closure. funelim (s_up_set b)=> /=. 
  apply /(iffP idP); rewrite mem_cat /sfrel /=.
  { move=> /orP[/base|/flatten_mapP[x]] //.
    by case: eqP=> // S /filter_lt/X/(_ a x erefl) /apply /(step S). }
  move: X=> /swap[[?->//|y ? /dup ? /filter_lt L /swap /(_ _ L a y erefl)]].
  move=> /apply ?; apply/orP; right; apply/flatten_mapP.
  exists y=> //. by case eqP.
Qed.

Lemma t_closure_lt a b : t_closure a b -> a < b.
Proof. by move=> /t_closureP /clos_trans_lt. Qed.

Lemma t_closure_trans : transitive t_closure.
Proof.
  move=> b a c /t_closureP ab /t_closureP bc.
  apply /t_closureP /clos_trans_tn1 /t_trans.
  { apply /clos_tn1_trans /ab. }
  exact: clos_tn1_trans.
Qed.

(* Computation of the (non-strict) upward set of a given element
 * w.r.t relation R derived from function `f`,
 * i.e. up_set(x) = { y | x = y \/ x R y } 
 *)
Definition up_set a := a :: s_up_set a.

Definition rt_closure a b := a \in up_set b. 

Lemma refl_t_rt a b :
  reflect (clos_refl T t_closure a b) (rt_closure a b).
Proof.
  rewrite /rt_closure /up_set. funelim (s_up_set b).
  apply /(iffP idP).
  { rewrite -cat_cons mem_cat in_cons => /orP[/orP[/eqP ->|]|].
    { exact: r_refl. }
    { constructor. rewrite /t_closure. funelim (s_up_set n).
      by rewrite mem_cat b. }
    constructor. rewrite /t_closure. funelim (s_up_set n).
    by rewrite mem_cat b. }
  case=> [b |]; last exact: mem_head.
  rewrite /t_closure in_cons. by funelim (s_up_set b) => ->.
Qed.

Lemma trans_refl_trans a b  {R : rel T}:
  clos_trans T R a b -> clos_refl_trans T R a b.
Proof.
  elim=> [|c d e ctcd crtcd ctde crtce]; first by constructor.
  apply /rt_trans; first exact: crtcd. exact: crtce.
Qed.

Lemma filter_clos_sub a b :
  clos_trans_n1 T (sfrel f\eq) a b -> clos_trans_n1 T (sfrel f) a b.
Proof.
  elim=> [c sfac | c d sfcd ctacn ctac].
  { apply /tn1_step. move: sfac.
    by rewrite /filter_neq /sfrel /= mem_filter => /andP[]. }
  apply /tn1_trans; last exact: ctac. move: sfcd. 
  by rewrite /filter_neq /sfrel /= mem_filter => /andP[].
Qed.

Lemma refl_eq_neq a b {R : relation T} :
  clos_refl T R a b -> (a == b) \/ R a b.
Proof. case; first by right. left. exact: eq_refl. Qed.

Lemma refl_trans_refl_rt a b :
  clos_refl_trans_n1 T (sfrel f) a b -> clos_refl T t_closure a b.
Proof.
  rewrite /sfrel /=. 
  elim=> [|c d sfcd crtac /refl_t_rt rtac]; first exact: r_refl.
  case: (c =P d) => [<-| /eqP neq].
  { apply /refl_t_rt. case: (refl_t_rt a c rtac) => [e|]; last exact: mem_head.
    by rewrite /rt_closure /up_set /t_closure in_cons => ->. }
  constructor. apply /t_closureP. elim: crtac => //.
  case: (a =P c) => [->|nac].
  { constructor. rewrite /sfrel /filter_neq /= mem_filter. apply /andP.
  split; first exact: neq. done. }
  apply /clos_trans_tn1 /t_trans.
  { move: (refl_eq_neq (refl_t_rt a c rtac)) => [/eqP //|tac].
  apply /clos_tn1_trans /t_closureP /tac. }
  constructor. rewrite /sfrel /filter_neq /= mem_filter. apply /andP.
  split; first exact: neq. done.
Qed.

Lemma rt_closure_refl : reflexive rt_closure.
Proof. move=> a. exact: mem_head. Qed.

(* Reflexive-transitive closure reflection lemma *)
Lemma rt_closureP a b :
  reflect (clos_refl_trans_n1 T (sfrel f) a b) (rt_closure a b).
Proof.
  apply /(iffP idP).
  { move=> /refl_t_rt. case => [c /t_closureP cac|]; last by constructor.
    by apply /clos_rt_rtn1 /trans_refl_trans /clos_tn1_trans /filter_clos_sub. }
  by move=> /refl_trans_refl_rt /refl_t_rt.
Qed.

Lemma rt_closure_trans : transitive rt_closure.
Proof.
  move=> b a c /rt_closureP ab /rt_closureP bc.
  apply/rt_closureP /clos_rt_rtn1 /rt_trans.
  apply/clos_rtn1_rt /ab. exact: clos_rtn1_rt.
Qed.

End well_founded.
