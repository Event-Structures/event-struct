From RelationAlgebra Require Import lattice boolean.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun.
From mathcomp Require Import eqtype choice order seq tuple.
From mathcomp Require Import fintype finfun fingraph finmap.
From eventstruct Require Import utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.

Local Open Scope order_scope.

(******************************************************************************)
(* Auxiliary definitions and lemmas about partial orders.                     *)
(*                                                                            *)
(******************************************************************************)

Section POrderUtils. 
Context {disp : unit} {T : porderType disp}.
Implicit Types (x y z : T).

Lemma le_ge_incomp x y : 
  [|| (x <= y), (x >= y) | (x >< y)].
Proof. 
  case: (x <= y)/idP=> //=.
  case: (y <= x)/idP=> //=.
  rewrite !negb_or=> /negP ? /negP ?; exact/andP.
Qed.

Lemma le_gt_incomp x y : 
  [|| (x <= y), (x > y) | (x >< y)].
Proof. 
  move: (le_ge_incomp x y)=> /or3P[->||->] //.
  rewrite le_eqVlt=> /orP[/eqP->|->] //.
  by rewrite le_refl.
Qed.

End POrderUtils.


Module Export MaxSup.
Section Def.
Context {disp : unit} {T : porderType disp}.
Implicit Types (s : seq T) (x : T).

(* TODO: generalize to arbitary pred? *)
Definition is_sup s x := 
  (x \in s) && all (fun y => y <= x) s.

(* TODO: generalize to arbitary pred? *)
Definition is_max s x := 
  (x \in s) && all (fun y => ~~ (x < y)) s.

Definition max_seq x s := 
  foldr Order.max x s.

End Def.

Section Theory.
Context {disp : unit} {T : orderType disp}.
Implicit Types (s : seq T) (x : T).

Lemma is_supP s x : 
  reflect (x \in s /\ {in s, forall y, y <= x}) (is_sup s x).
Proof. exact/(andPP idP allP). Qed.

Lemma is_maxP s x : 
  reflect (x \in s /\ {in s, forall y, ~~ (x < y)}) (is_max s x).
Proof. exact/(andPP idP allP). Qed.

Lemma is_sup_in s x : 
  is_sup s x -> x \in s.
Proof. by move=> /is_supP[]. Qed.
  
Lemma is_sup_uniq X x y :
  is_sup X x -> is_sup X y -> x = y.
Proof.
  case/is_supP=> i l.
  case/is_supP=> /l /[swap]/(_ _ i) lxy *.
  by apply/le_anti; rewrite lxy.
Qed.

Lemma is_sup0 x :
  ~~ is_sup [::] x.
Proof. done. Qed.

Lemma is_sup_eq s1 s2 : 
  s1 =i s2 -> is_sup s1 =1 is_sup s2.
Proof. by move=> e x; rewrite /is_sup e (eq_all_r e). Qed.

Lemma is_sup1 x y :
  (is_sup [:: x] y) = (x == y).
Proof.
  rewrite /is_sup inE /= andbT andb_idr eq_sym //.
  by move=> /eqP->; rewrite lexx.
Qed.    

Lemma max_seq_in d s : 
  max_seq d s \in d :: s.
Proof.
  elim: s=> [|x s] //=; rewrite !inE //.
  by case: leP; rewrite ?eqxx //= => + /orP[|] ->. 
Qed.

Lemma max_seq_dflt_le d s : 
  d <= max_seq d s.
Proof. 
  elim s=> //= x {}s IH.
  apply/(le_trans IH).
  by rewrite le_maxr lexx.
Qed.

Lemma max_seq_in_le d s x : 
  x \in s -> x <= max_seq d s.
Proof. 
  elim s=> //= y {}s IH.
  rewrite inE le_maxr=> /orP[/eqP->|/IH->] //=.
  by rewrite lexx.
Qed.

Lemma max_seq_all d s x : 
  d <= x -> all (<=%O^~ x) s = (max_seq d s <= x).
Proof. 
  move=> led; apply/idP/idP.
  - move: (max_seq_in d s); rewrite inE=> /orP[/eqP->|] //. 
    by move=> /[swap] /allP; apply.
  elim s=> //= y {}s IH.
  by rewrite le_maxl=> /andP[->] /IH ->.  
Qed.

Lemma max_seq_all_dflt d s :
  all (<=%O^~ d) s = (max_seq d s == d).
Proof.
  rewrite (@max_seq_all d) le_eqVlt orb_idr //.
  move=> /ltW ?; apply/eqP/le_anti/andP; split=> //.
  exact/max_seq_dflt_le.
Qed.

Lemma is_sup_max_seqE d s x : 
  is_sup s x -> max_seq d s = Order.max d x.
Proof. 
  move=> /is_supP[xin lex].
  apply/le_anti/andP; split; case: (leP d)=> // xd; last 2 first.
  - exact/max_seq_in_le.
  - exact/max_seq_dflt_le.
  - rewrite -max_seq_all //; exact/allP.
  rewrite le_eqVlt -max_seq_all_dflt.
  apply/orP; left; apply/allP=> y /lex. 
  move=> /le_trans; apply; exact/ltW.
Qed.

Lemma is_sup_le_max_seqE d s x :
  d <= x -> is_sup s x -> max_seq d s = x.
Proof. move=> dx supx; rewrite -(max_r dx); exact/is_sup_max_seqE. Qed.

Lemma max_seq_sup d s x : 
  max_seq d s \in s -> is_sup s (max_seq d s).
Proof. move=> max_in; apply/is_supP; split=> //; exact/max_seq_in_le. Qed.

Lemma is_supE d s x : 
  d <= x -> (is_sup s x) = (x \in s) && (max_seq d s == x).
Proof.
  move=> dx; apply/idP/idP; last first.
  - move=> /andP[] /[swap] /eqP<-; exact/max_seq_sup.
  move=> /[dup] /is_sup_in -> /(is_sup_max_seqE d) -> /=.
  by rewrite max_r.    
Qed.

Section WithBottom.
Context {d : T}.
Hypothesis (dbot : forall x, d <= x).

Lemma max_seq_inNnil s : 
  s != [::] -> max_seq d s \in s.
Proof.
  elim: s=> // x s IH /= _. 
  case: (s == [::])/eqP=> [->|/eqP nl] /=.
  - rewrite max_l ?inE //.
  by case: leP; rewrite ?inE ?eqxx ?IH.
Qed.

Lemma max_set_eq s1 s2 :
  s1 =i s2 -> max_seq d s1 = max_seq d s2.
Proof.
  move=> eqm; case: (s1 == [::])/idP.
  - move=> /[dup] + /eqP ->. 
    by rewrite (eq_mem0 eqm)=> /eqP->.
  move=> /negP; rewrite (eq_mem0 eqm)=> neq.
  apply/is_sup_le_max_seqE=> //.
  apply/is_supP; split.
  - by rewrite eqm; apply/max_seq_inNnil. 
  by move=> x; rewrite eqm=> /max_seq_in_le. 
Qed.

Lemma is_sup_NnilE s x :
  s != [::] -> is_sup s x = (max_seq d s == x).
Proof. 
  rewrite (@is_supE d) // => neq.
  apply/idP/idP=> [/andP[? ->]|/eqP<-] //.
  rewrite eqxx andbT; exact/max_seq_inNnil.
Qed.

End WithBottom.

Section Monotone.
Variables (f : T -> T) (s : seq T) (x : T).

Hypothesis (finj : injective f).
Hypothesis (fmon : {mono f : x y / x <= y}).

Lemma is_sup_mon : 
  is_sup [seq f y | y <- s] (f x) = is_sup s x.
Proof. 
  rewrite /is_sup mem_map // all_map.
  apply/andb_id2l=> _; apply/eq_all.
  move=> y /=; exact/fmon. 
Qed.

End Monotone.

End Theory.

End MaxSup.

Module DwFinPOrder.

Module Export DwFinPOrder.
Section ClassDef. 

Record mixin_of (T0 : Type) 
                (b : Order.POrder.class_of T0)
                (* TODO: parametrize by disp? *)
                (T := Order.POrder.Pack tt b) := Mixin {
  pideal : T -> {fset T};
  _ : forall x y : T, x \in (pideal y) = (x <= y);
}.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base  : Order.POrder.class_of T;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Order.POrder.class_of.

Structure type := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack :=
  fun bT b & phant_id (@Order.POrder.class tt bT) b =>
  fun m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @Order.POrder.Pack tt cT class.
End ClassDef.
End DwFinPOrder.

Module Export Exports.
Coercion base : class_of >-> Order.POrder.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> Order.POrder.type.
Notation dwFinPOrderType := type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Notation DwFinPOrderType T m := (@pack T _ _ id m).
End Exports.

Module Export Def.
Section Def.
Context {T : dwFinPOrderType}.

Definition pideal : T -> {fset T} := 
  DwFinPOrder.pideal (DwFinPOrder.class T).

Definition up_clos : pred T -> pred T :=
  fun P x => [exists y : pideal x, P (val y)].

End Def.
End Def.

Module Export Theory.
Section Theory.
Context {T : dwFinPOrderType}.
Implicit Types (x y : T) (P Q : pred T).

Lemma pidealE x y :
  x \in (pideal y) = (x <= y).
Proof. by move: x y; case: T=> [? [? []]]. Qed.

(* TODO: rename? *)
Lemma pidealx x : 
  x \in pideal x.
Proof. by rewrite pidealE. Qed.

Lemma up_closP P x : 
  reflect (exists2 y, y <= x & y \in P) (x \in up_clos P). 
Proof. 
  apply/(equivP idP). 
  rewrite /up_clos !unfold_in /=; split.
  - move=> /existsP /= [y]; move: (valP y). 
    by rewrite pidealE=> ??; exists (val y). 
  move=> [y] le_yx Py; apply/existsP.
  have: y \in pideal x by rewrite pidealE.
  by move=> yi; exists (Sub y yi).
Qed.

(* Kuratowski closure axioms *)

Lemma up_clos0 : 
  up_clos (pred0 : pred T) =1 pred0.
Proof. 
  move=> x; apply/idP=> /=. 
  by move=> /up_closP[y].
Qed.

Lemma up_clos_ext P : 
  {subset P <= up_clos P}.
Proof. by move=> x Px; apply/up_closP; exists x. Qed.

Lemma up_clos_idemp P : 
  up_clos (up_clos P) =1 up_clos P.
Proof. 
  move=>>; apply/idP/idP; last exact/up_clos_ext. 
  case/up_closP=>> l /up_closP[x] /le_trans/(_ l) *.
  apply/up_closP; by exists x. 
Qed.

Lemma up_closU P Q : 
  up_clos ([predU P & Q]) =1 [predU (up_clos P) & (up_clos Q)].
Proof. 
  move=> x; apply/idP/idP=> /=. 
  - move=> /up_closP[y] le_yx; rewrite inE. 
    by move=> /orP[] ?; apply/orP; [left | right]; apply/up_closP; exists y.
   move=> /orP[] /up_closP[y] le_xy y_in; apply/up_closP; exists y=> //=. 
   all: by rewrite !inE y_in ?orbT.
Qed.

(* ************************* *)

Lemma up_clos_subs P Q : 
  {subsumes P <= Q : x y / y <= x } <-> {subset (up_clos P) <= (up_clos Q)}. 
Proof. 
  split=> [subs x | sub x]; last first.
  - move: up_clos_ext=> /[apply] x_in.
    by move: (sub x x_in)=> /up_closP[y] ??; exists y. 
  move=> /up_closP[y] le_yx Py.
  apply/up_closP; move: (subs y Py)=> [z] z_in le_zy.
  exists z=> //; exact/(le_trans le_zy).
Qed.

End Theory.
End Theory.

End DwFinPOrder.

Export DwFinPOrder.Exports.
Export DwFinPOrder.Def.
Export DwFinPOrder.Theory.
