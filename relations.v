From Equations Require Import Equations.
From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat ssrfun fintype seq order.
From Coq Require Import Relations Program.Basics.
From event_struct Require Import utilities wftype.

Set Implicit Arguments.
(*Unset Strict Implicit.*)
Unset Printing Implicit Defensive.
Set Equations Transparent.

Import Order.LTheory.
Open Scope order_scope.

Section well_founded.

Context {T : wfType}.

Definition rel_of_fun (f : T -> seq T) : rel T :=
  [rel a b | a \in f b]. (*[seq x <- f b | x != b]].*)

Variable (f : T -> seq T).

Hypothesis descend : forall x n, x \in f n -> x < n.

(*Lemma filter_lt n k : k \in [seq x <- f n | x != n] -> k < n.
Proof.
  by rewrite mem_filter lt_neqAle => /andP [] -> /p ->.
Qed.*)

Lemma rel_sublt a b : (rel_of_fun f) a b -> a < b.
Proof.
  rewrite/rel_of_fun /=. exact: descend.
Qed.

(* Well-founded relation closure definition *)
Equations(noind) t_closure (n : T) : seq T by wf n (<%O : rel T) :=
  t_closure n := (f n) ++ flatten
                  (map 
                      (fun x => if x \in (f n) =P true is ReflectT pf then
                        t_closure x
                      else [::]) 
                      (f n)
                  ).

Definition rel_of_closure (a b : T) : bool := a \in t_closure b.

Lemma cat_eq (s1 s2 s3 : seq T) : s1 = s2 <-> s3 ++ s1 = s3 ++ s2.
Proof.
  elim: s3.
  { split=> /= [-> |] //. }
  move=> h xs IHs. split=> [/IHs |].
  { by rewrite !cat_cons => ->. }
  rewrite !cat_cons => /eqP.
  by rewrite eqseq_cons IHs => /andP [] ? /eqP.
Qed.

Lemma rel_of_closure_sublt a b : rel_of_closure a b -> a < b.
Proof.
  rewrite /rel_of_closure.
  move: b a.
  apply: wf_ind => b IH a.
  rewrite /t_closure /Subterm.FixWf Fix_eq.
  { rewrite {1}/t_closure_functional mem_cat=> /orP [/descend //|].
    case/flatten_mapP=> x /descend xinf.
    case: eqP.
    { move=> /descend /IH /apply ax. apply: lt_trans. exact: ax. done. }
    done. }
  move=> x g h H. rewrite /t_closure_functional. apply/eqP.
  rewrite eqseq_cat //=. apply/andP. split=> //=. apply/eqP.
  congr flatten. apply/eq_in_map. move=> y /descend. case: eqP=> //=.
Qed.

Lemma clos_trans_sublt a b : clos_trans_n1 T (rel_of_fun f) a b -> a < b.
Proof.
  rewrite/rel_of_fun /=.
  elim=> [x /descend // | x y xfy acx ax].
  apply: lt_trans; first by apply: ax.
  exact: descend.
Qed. 

(* Well-founded relations properties *)
Lemma closureP a b : 
  reflect (clos_trans_n1 T (rel_of_fun f) a b) (rel_of_closure a b).
Proof.
  rewrite /rel_of_closure.
  move: b a. apply: wf_ind=> b IH a.
  apply /(iffP idP).
  { rewrite /t_closure /Subterm.FixWf Fix_eq.
    { rewrite {1}/t_closure_functional mem_cat => /orP [].
      { by constructor. }
      case/flatten_mapP=> x xinf. case: eqP.
      { move=> /descend /IH /apply H. apply /clos_trans_tn1 /t_trans.
        { apply /clos_tn1_trans. exact: H. }
        by constructor. }
      done. }
    move=> x g h H. apply/eqP.
    rewrite eqseq_cat //=. apply/andP. split=> //=. apply/eqP.
    congr flatten. apply/eq_in_map.
    move=> y /descend. case: eqP=> //=. }
  move=> closab.
  move: (clos_tn1_trans _ (fun x x0 => rel_of_fun f x x0) _ _ closab)=> ctnab.
  move: (clos_trans_tn1 _ (fun x x0 => rel_of_fun f x x0) _ _ ctnab)=> ctab.
  move: ctab IH.
  case.
  { rewrite /rel_of_fun /= => c afc IH.
    rewrite /t_closure /Subterm.FixWf Fix_eq.
    { by rewrite {1}/t_closure_functional mem_cat afc. }
    move=> x g h H. apply/eqP.
    rewrite eqseq_cat //=. apply/andP. split=> //=. apply/eqP.
    congr flatten. apply/eq_in_map.
    move=> y /descend. case: eqP=> //=. }
  move=> c d. rewrite /rel_of_fun /= => cfd ctac IHd.
  rewrite /t_closure /Subterm.FixWf Fix_eq.
  { rewrite {1}/t_closure_functional mem_cat. apply/orP.
    right. apply/flatten_mapP. exists c=> //=. case: eqP=> //=.
    move=> _. apply/IHd=> //=. exact: descend. }
  move=> x g h H. apply/eqP.
  rewrite eqseq_cat //=. apply/andP. split=> //=. apply/eqP.
  congr flatten. apply/eq_in_map.
  move=> y /descend. case: eqP=> //=.
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
  reflect (clos_refl_trans_n1 T (rel_of_fun f) a b) (rt_closure_rel a b).
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
  { right. move: cfd. rewrite /rel_of_fun /=.
    rewrite /t_closure /Subterm.FixWf Fix_eq.
    { by rewrite {1}/t_closure_functional mem_cat => ->. }
  move=> x g h H. apply/eqP.
  rewrite eqseq_cat //=. apply/andP. split=> //=. apply/eqP.
  congr flatten. apply/eq_in_map.
  move=> y /descend. case: eqP=> //=. }
  right. move: (closureP a c)=> refl. move: (refl ac)=> cac.
  apply /(closureP a d) /clos_trans_tn1 /t_trans.
  { apply /clos_tn1_trans. exact: cac. }
  by constructor.
Qed.

End well_founded.
