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

(* Reflexive-transitive closure reflection lemma *)
Lemma rt_closureP a b :
  reflect (clos_refl_trans_n1 T (sfrel f) a b) (rt_closure a b).
Proof.
  apply /(iffP idP).
  { rewrite /rt_closure. 
    rewrite in_cons=> /orP[/eqP -> | atb].
    { constructor. }
    move: (t_closureP a b). 
    rewrite /t_closure => refl. move: (refl atb). 
    elim=> [c cfd | c d cfd st rt].
    { apply: rtn1_trans; last by constructor.
      move: cfd. rewrite /sfrel /filter_neq //=.
      rewrite mem_filter. by move=> /andP [??]. }
    apply: rtn1_trans; last exact: rt.
    move: cfd. rewrite /sfrel /filter_neq //=.
    rewrite mem_filter. move=> /andP [? H]. exact: H. }
  move=> cab. rewrite /rt_closure /up_set.
  rewrite in_cons. apply/orP.
  elim: cab => [| c d st rt [/eqP -> | efd]]; first by left.
  { case: (c =P d)=> [eq| /eqP neq] //=; first by left.
    right. move: st. rewrite /sfrel /=.
    funelim (s_up_set d) => cfn. rewrite /hack mem_cat. apply/orP. left.
    by rewrite mem_filter cfn neq. }
  case: (c =P d)=> [<-| /eqP neq] //=; first by right. 
  right. move: (t_closureP a c)=> refl. move: (refl efd)=> ct.
  apply /(t_closureP a d) /clos_trans_tn1 /t_trans.
  { apply /clos_tn1_trans. exact: ct. }
  apply: t_step. rewrite /sfrel /filter_neq //= mem_filter neq. exact: st.
Qed.

Lemma rt_closure_refl : reflexive rt_closure.
Proof. move=> a. exact: mem_head. Qed.

Lemma rt_closure_trans : transitive rt_closure.
Proof.
  move=> b a c /rt_closureP ab /rt_closureP bc.
  apply/rt_closureP /clos_rt_rtn1 /rt_trans.
  apply/clos_rtn1_rt /ab. exact: clos_rtn1_rt.
Qed.

End well_founded.
