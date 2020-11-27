From Coq Require Import Lia.
From Coq Require Import Relations Program.Basics ssrsearch.
From mathcomp Require Import ssreflect ssrbool eqtype ssrfun seq order.
From Equations Require Import Equations.
From event_struct Require Import utilities wftype.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Set Equations Transparent.

Import Order.LTheory.
Open Scope order_scope.

Section well_founded.

Definition sfrel {T : eqType} (f : T -> seq T) : rel T :=
  [rel a b | b \in f a].

Definition filter_neq {T : eqType} (f : T -> seq T) : T -> seq T :=
  fun n => filter^~ (f n) (fun x => x != n).

Notation "f '\eq'" := (filter_neq f) (at level 5, format "f '\eq'").

Context {T : wfType}.

Variable (f : T -> seq T).

Hypothesis descend : forall x n, x \in f n -> x <= n.

Lemma filter_lt n k : k \in f\eq n -> k < n.
Proof. by rewrite mem_filter lt_neqAle => /andP[] -> /descend ->. Qed.

Lemma rel_sublt a b : (sfrel f\eq) a b -> b < a.
Proof. rewrite/sfrel /=. exact: filter_lt. Qed.

(* Computation of the strict upward set of a given element
 * w.r.t relation R derived from function `f`,
 * i.e. s_up_set(x) = { y | x R y } 
 *)
Equations(noind) s_up_set (n : T) : seq T by wf n (<%O : rel T) :=
  s_up_set n := 
    let ys := f\eq n in 
    let ps := flatten (map^~ ys (fun x => 
      if x \in ys =P true is ReflectT pf then
        s_up_set x
      else 
        [::]
    )) in
    ys ++ ps.
Next Obligation. exact: filter_lt. Qed.

Definition t_closure (a b : T) : bool := b \in s_up_set a.

Lemma ext_s_up_set (x : T) (g h : forall y : T, y < x -> seq T) :
  (forall (y : T) (p : y < x), g y p = h y p) ->
    s_up_set_functional x g = s_up_set_functional x h.
Proof.
  move=> H. rewrite /s_up_set_functional. apply/eqP.
  rewrite eqseq_cat //=. apply/andP. split=> //=. apply/eqP.
  congr flatten. apply/eq_in_map. move=> y /filter_lt. case: eqP=> //=.
Qed.

Lemma t_closure_lt a b : t_closure a b -> b < a.
Proof.
  rewrite /t_closure.
  move: a b. apply: wf_ind => a IH b.
  rewrite /s_up_set /Subterm.FixWf Fix_eq; last by apply: ext_s_up_set.
  rewrite {1}/s_up_set_functional mem_cat => /orP [/filter_lt //|].
  case/flatten_mapP=> x /filter_lt xinf.
  case: eqP => //. move=> /filter_lt /IH /apply ax. 
  by apply: lt_trans; first apply: ax.
Qed.

Lemma clos_trans_lt a b : clos_trans_n1 T (sfrel f\eq) a b -> b < a.
Proof.
  rewrite/sfrel /=.
  elim=> [x /filter_lt // | x y xfy acx ax].
  apply: lt_trans; last by apply: ax.
  exact: filter_lt.
Qed. 

(* Transitive closure reflection lemma *)
Lemma t_closureP a b : 
  reflect (clos_trans_1n T (sfrel f\eq) a b) (t_closure a b).
Proof.
  rewrite /t_closure.
  move: a b. apply: wf_ind=> a IH b.
  apply /(iffP idP).
  { rewrite /s_up_set /Subterm.FixWf Fix_eq; last by apply: ext_s_up_set.
    rewrite {1}/s_up_set_functional mem_cat => /orP [].
    { by constructor. }
    case/flatten_mapP=> x xinf. case: eqP=> //=.
    move=> /filter_lt /IH /apply H.
    apply: Relation_Operators.t1n_trans; last exact H.
    exact xinf. }
  move=> ctab. move: ctab IH. case.
  { rewrite /sfrel /= => c afc IH.
    rewrite /s_up_set /Subterm.FixWf Fix_eq; last by apply: ext_s_up_set.
    by rewrite {1}/s_up_set_functional mem_cat afc. }
  move=> c d. rewrite /sfrel /= => cfd ctac IHd.
  rewrite /s_up_set /Subterm.FixWf Fix_eq; last by apply: ext_s_up_set.
  rewrite {1}/s_up_set_functional mem_cat. apply/orP.
  right. apply/flatten_mapP. exists c=> //=. case: eqP=> //=.
  move=> _. apply/IHd=> //=. exact: filter_lt.
Qed.


(* Computation of the (non-strict) upward set of a given element
 * w.r.t relation R derived from function `f`,
 * i.e. up_set(x) = { y | x = y \/ x R y } 
 *)
Definition up_set a := a :: s_up_set a.

Definition rt_closure a b := b \in up_set a. 

Lemma rt_closure_refl a : rt_closure a a.
Proof. rewrite /rt_closure /up_set. exact: mem_head. Qed.

Lemma rt_closure_trans a b c :
  rt_closure a b -> rt_closure b c -> rt_closure a c.
Proof.
  rewrite /rt_closure.
  rewrite !in_cons => /orP [/eqP -> //|].
  move=> ba /orP [/eqP -> //|].
  { by rewrite ba. }
  move=> cb. apply /orP. right.
  apply /t_closureP. apply: clos_trans_t1n. apply: t_trans.
  { apply /clos_t1n_trans /t_closureP. exact: ba. }
  apply /clos_t1n_trans /t_closureP. exact: cb.
Qed.

(* Reflexive-transitive closure reflection lemma *)
Lemma rt_closureP a b :
  reflect (clos_refl_trans_1n T (sfrel f) a b) (rt_closure a b).
Proof.
  apply /(iffP idP).
  { rewrite /rt_closure. 
    rewrite in_cons=> /orP[/eqP -> | atb].
    { constructor. }
    move: (t_closureP a b). 
    rewrite /t_closure => refl. move: (refl atb). 
    elim=> [c d cfd | c d e cfd st rt].
    { apply: Relation_Operators.rt1n_trans; last by constructor.
      move: cfd. rewrite /sfrel /filter_neq //=.
      rewrite mem_filter. by move=> /andP [??]. }
    apply: Relation_Operators.rt1n_trans; last exact: rt.
    move: cfd. rewrite /sfrel /filter_neq //=.
    rewrite mem_filter. move=> /andP [? H]. exact: H. }
  move=> cab. rewrite /rt_closure /up_set.
  rewrite in_cons. apply/orP.
  elim: cab => [| c d e st rt [/eqP -> | efd]]; first by left.
  { case: (d =P c)=> [eq|neq] //=; first by left.
    right. move: st. rewrite /sfrel /=.
    rewrite /s_up_set /Subterm.FixWf Fix_eq; last by apply: ext_s_up_set.
    rewrite {1}/s_up_set_functional mem_cat /filter_neq mem_filter => ->.
     apply /orP. left. by apply /predD1P. }
  case: (d =P c)=> [<-|neq] //=; first by right. 
  right. move: (t_closureP d e)=> refl. move: (refl efd)=> ct.
  apply /(t_closureP c e) /clos_trans_t1n /t_trans; first last.
  { apply: clos_t1n_trans. exact: ct. }
  apply: t_step. rewrite /sfrel /filter_neq //=. 
  rewrite mem_filter. by apply /predD1P. 
Qed.

End well_founded.
