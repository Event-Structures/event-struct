From Coq Require Import Lia.
From Coq Require Import Relations Program.Basics.
From mathcomp Require Import ssreflect ssrbool eqtype ssrfun seq order.
From Equations Require Import Equations.
From event_struct Require Import utilities wftype.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Set Equations Transparent.

Import Order.LTheory.
Open Scope order_scope.

Section well_founded.

Context {T : wfType}.

Definition filter_neq (f : T -> seq T) : T -> seq T :=
  fun n => filter (fun x => x != n) (f n).

Definition sfrel (f : T -> seq T) : rel T :=
  [rel a b | a \in (filter_neq f) b].

Variable (f : T -> seq T).

Hypothesis descend : forall x n, x \in f n -> x <= n.

Lemma filter_lt n k : k \in (filter_neq f n) -> k < n.
Proof. by rewrite mem_filter lt_neqAle => /andP[] -> /descend ->. Qed.

Lemma rel_sublt a b : (sfrel f) a b -> a < b.
Proof. rewrite/sfrel /=. exact: filter_lt. Qed.

(* Well-founded relation closure definition *)
Equations(noind) t_closure (n : T) : seq T by wf n (<%O : rel T) :=
  t_closure n := 
    let ys := (filter_neq f n) in 
    let ps := flatten (map^~ ys (fun x => 
      if x \in ys =P true is ReflectT pf then
        t_closure x
      else 
        [::]
    )) in
    ys ++ ps.
Next Obligation. exact: filter_lt. Qed.

Definition rel_of_closure (a b : T) : bool := a \in t_closure b.

Lemma ext_t_closure (x : T) (g h : forall y : T, y < x -> seq T) :
  (forall (y : T) (p : y < x), g y p = h y p) ->
    t_closure_functional x g = t_closure_functional x h.
Proof.
  move=> H. rewrite /t_closure_functional. apply/eqP.
  rewrite eqseq_cat //=. apply/andP. split=> //=. apply/eqP.
  congr flatten. apply/eq_in_map. move=> y /filter_lt. case: eqP=> //=.
Qed.

Lemma rel_of_closure_sublt a b : rel_of_closure a b -> a < b.
Proof.
  rewrite /rel_of_closure.
  move: b a. apply: wf_ind => b IH a.
  rewrite /t_closure /Subterm.FixWf Fix_eq; last by apply: ext_t_closure.
  rewrite {1}/t_closure_functional mem_cat => /orP [/filter_lt //|].
  case/flatten_mapP=> x /filter_lt xinf.
  case: eqP => //. move=> /filter_lt /IH /apply ax. 
  by apply: lt_trans; first apply: ax.
Qed.

Lemma clos_trans_sublt a b : clos_trans_n1 T (sfrel f) a b -> a < b.
Proof.
  rewrite/sfrel /=.
  elim=> [x /filter_lt // | x y xfy acx ax].
  apply: lt_trans; first by apply: ax.
  exact: filter_lt.
Qed. 

(* Well-founded relations properties *)
Lemma closureP a b : 
  reflect (clos_trans_n1 T (sfrel f) a b) (rel_of_closure a b).
Proof.
  rewrite /rel_of_closure.
  move: b a. apply: wf_ind=> b IH a.
  apply /(iffP idP).
  { rewrite /t_closure /Subterm.FixWf Fix_eq; last by apply: ext_t_closure.
    rewrite {1}/t_closure_functional mem_cat => /orP [].
    { by constructor. }
    case/flatten_mapP=> x xinf. case: eqP=> //=.
    move=> /filter_lt /IH /apply H. 
    apply /clos_trans_tn1 /t_trans; first last.
    { constructor. apply: xinf. }
    apply /clos_tn1_trans. exact: H. }
  move=> ctab. move: ctab IH. case.
  { rewrite /sfrel /= => c afc IH.
    rewrite /t_closure /Subterm.FixWf Fix_eq; last by apply: ext_t_closure.
    by rewrite {1}/t_closure_functional mem_cat afc. }
  move=> c d. rewrite /sfrel /= => cfd ctac IHd.
  rewrite /t_closure /Subterm.FixWf Fix_eq; last by apply: ext_t_closure.
  rewrite {1}/t_closure_functional mem_cat. apply/orP.
  right. apply/flatten_mapP. exists c=> //=. case: eqP=> //=.
  move=> _. apply/IHd=> //=. exact: filter_lt.
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
  reflect (clos_refl_trans_n1 T (sfrel f) a b) (rt_closure_rel a b).
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
  { right. move: cfd. rewrite /sfrel /=.
    rewrite /t_closure /Subterm.FixWf Fix_eq; last by apply: ext_t_closure.
    by rewrite {1}/t_closure_functional mem_cat => ->. }
  right. move: (closureP a c)=> refl. move: (refl ac)=> cac.
  apply /(closureP a d) /clos_trans_tn1 /t_trans.
  { apply /clos_tn1_trans. exact: cac. }
  by constructor.
Qed.

End well_founded.
