From RelationAlgebra Require Import lattice boolean.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun.
From mathcomp Require Import eqtype choice order seq tuple path div.
From mathcomp Require Import fintype finfun fingraph finmap.
From eventstruct Require Import utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.

Local Open Scope fset_scope.
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


Section Closure.
Context {disp : unit} {T : porderType disp}.
Implicit Types (x y z : T) (X : pred T).

Definition dw_closed (X : pred T) : Prop :=
  (* ca · [X] ≦ [X] · ca; *)
  forall x y, x <= y -> X y -> X x.

Lemma eq_dw_closed X Y : 
  X =1 Y -> dw_closed X <-> dw_closed Y. 
Proof. move=> e; split=> dw ??; [rewrite -?e | rewrite ?e]; exact/dw. Qed.

End Closure.

Section POrderMorph.
Context {dispT : unit} {dispU : unit}. 
Context {T : porderType dispT} {U : porderType dispU}.
Implicit Types (f : T -> U).
Implicit Types (x y z : T).

Lemma le_homo_lt_img f x y : 
  {homo f : x y / x <= y} -> (f x < f y) -> (x < y) || (x >< y).
Proof.
  case lt_xy: (x < y)=> //= fmon lt_fxy.
  apply/negP=> /orP [].
  - rewrite le_eqVlt lt_xy orbF.
    by move: lt_fxy=> /[swap] /eqP<-; rewrite ltxx.
  move=> /fmon le_fyx.
  move: (lt_le_asym (f x) (f y)).
  by move=> /andP; apply; split=> //.
Qed.

Lemma lt_homo_le_img f x y : 
  {homo f : x y / x < y} -> (f x <= f y) -> (x <= y) || (x >< y).
Proof.
  move=> fmon le_fxy.
  move: (le_gt_incomp x y)=> /or3P[-> | | ->] //.
  move=> /fmon lt_fyx; exfalso.
  move: (lt_le_asym (f y) (f x)).
  by move=> /andP; apply; split=> //.
Qed.

Lemma le_homo_mono f : 
  {homo f : x y / x <= y} -> {ahomo f : x y / x <= y} -> 
  {mono f : x y / x <= y}.
Proof. 
  move=> fmon frefl x y. 
  apply/idP/idP; [exact/frefl | exact/fmon]. 
Qed.

Lemma cancel_le_ahomo_homo f g : cancel g f ->
  {ahomo f : x y / x <= y} -> {homo g : x y / x <= y}.
Proof. by move=> K fmon x y le_xy; apply/fmon; rewrite !K. Qed.

Lemma le_mono_incomp f :
  {mono f : x y / x <= y} -> { mono f : x y / x >< y }.
Proof.
  move=> femb x y; apply: negbLR.  
  by rewrite !negbK /Order.comparable !femb.
Qed.

Lemma le_homo_bij_total f : bijective f -> {homo f : x y / x <= y} ->
  total (<=%O : rel T) -> total (<=%O : rel U).
Proof. 
  case=> g Kf Kg fmon tot x y.
  by move: (tot (g x) (g y))=> /orP[] /fmon; rewrite !Kg=> ->. 
Qed.  

(* TODO: equivalent to mathcomp.ssreflect.order.le_mono *)
Lemma lt_homo_total_mono f : {homo f : x y / x < y} -> total (<=%O : rel T) ->
  { mono f : e1 e2 / e1 <= e2 }.
Proof.
  move=> fmon tot x y. 
  apply/idP/idP; last exact/ltW_homo. 
  move=> /(lt_homo_le_img fmon)=> /orP[] //.
  by rewrite /Order.comparable; move: (tot x y) ->.  
Qed.

Lemma dw_closed_preim f P : 
  {homo f : x y / x <= y} -> dw_closed P -> dw_closed (preim f P).
Proof. move=> fmon dw_clos=> x y /fmon; exact/dw_clos. Qed.

End POrderMorph.

Section FinPOrderMorph.
Context {dispT : unit} {dispU : unit}. 
Context {T : finPOrderType dispT} {U : finPOrderType dispU}.
Implicit Types (f : T -> U) (g : U -> T).
Implicit Types (x y z : T).

Lemma inj_le_homo_mono f g : injective f -> injective g ->
  {homo f : x y / x <= y} -> {homo g : x y / x <= y} -> {mono f : x y / x <= y}.
Proof. 
  move=> finj ginj fmon gmon.
  move=> e1 e2; apply/idP/idP; last exact/fmon.
  pose h := g \o f. 
  have hmon: {homo h : x y / x <= y}.
  - by move=> ?? /fmon /gmon. 
  have : injective h by exact/inj_comp. 
  move=> /cycle_orbit cyc.
  pose o1 := order h e1.
  pose o2 := order h e2.
  pose o  := lcmn o1 o2.
  have {2}<-: iter ((o %/ o1) * o1) h e1 = e1.
  - rewrite iter_mul_eq /o1 //.
    apply/(iter_order_cycle (cyc e1)); exact/in_orbit.
  have {2}<-: iter ((o %/ o2) * o2) h e2 = e2.
  - rewrite iter_mul_eq /o2 //.
    apply/(iter_order_cycle (cyc e2)); exact/in_orbit.
  rewrite !divnK; last first. 
  - exact/dvdn_lcml.
  - exact/dvdn_lcmr.
  have: o = lcmn o1 o2 by done.
  case o=> [|{}o]; last first.
  - rewrite !iterSr=> ??; apply/homo_iter=> //; exact/gmon.
  move=> /esym /eqP. 
  rewrite eqn0Ngt lcmn_gt0 negb_and ?/o1 ?/o2.
  move: (order_gt0 h e1) (order_gt0 h e2).
  by move=> ++ /orP[/negP|/negP]. 
Qed.

End FinPOrderMorph.

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


Section DwSurjective.
Context {dispT : unit} {T : porderType dispT}.
Context {dispU : unit} {U : porderType dispU}.
Implicit Types (f : T -> U).
Implicit Types (x y z : T).

(* TODO: consult literature to find relevant theory *)
Definition dw_surjective f := 
  forall x, {in (<= f x), surjective f}.

Lemma eq_dw_surj f : 
  dw_surjective f -> forall g, f =1 g -> dw_surjective g.
Proof. by move=> fdw g eqf x y; rewrite -?eqf=> /fdw [z] <-; exists z. Qed.

Lemma surj_dw_surj f : 
  surjective f -> dw_surjective f.
Proof. by move=> fsurj x y _; move: (fsurj y)=> [z] <-; exists z. Qed.

Lemma dw_surj_closed f (X : pred T) (Y : pred U) : 
  {ahomo f : x y / x <= y} -> dw_surjective f -> {in Y, surjective f} -> 
  (preim f Y) =1 X -> dw_closed X -> dw_closed Y.
Proof. 
  move=> fmon fdw fsurj fpreim dwX x y. 
  move=> /[swap] /[dup] /fsurj [y'] <-.
  move=> /[swap] /[dup] /fdw=> [[x']] <-. 
  by move=> /fmon /dwX; rewrite -fpreim -fpreim. 
Qed.

End DwSurjective.


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
Implicit Types (x : T) (X : {fset T}).

Definition pideal : T -> {fset T} := 
  DwFinPOrder.pideal (DwFinPOrder.class T).

Definition fin_ideal X : {fset T} := 
  \bigcup_(x <- X) (pideal x).

Definition up_clos : pred T -> pred T :=
  fun P x => [exists y : pideal x, P (val y)].

Definition dw_closedb X := 
  [forall x : fin_ideal X, val x \in X].

End Def.

Section Homo.
Context {T : dwFinPOrderType} {U : dwFinPOrderType}.
Implicit Types (f : T -> U).

Definition homo_pideal f := 
 forall x, pideal (f x) `<=` f @` (pideal x).

End Homo.
End Def.

Module Export Theory.
Section Theory.
Context {T : dwFinPOrderType}.
Implicit Types (x y : T) (X : {fset T}).
Implicit Types (P Q : pred T).

Lemma pidealE x y :
  x \in (pideal y) = (x <= y).
Proof. by move: x y; case: T=> [? [? []]]. Qed.

(* TODO: rename? *)
Lemma pidealx x : 
  x \in pideal x.
Proof. by rewrite pidealE. Qed.

Lemma fin_idealP X x : 
  reflect (exists2 y, y \in X & x <= y) (x \in fin_ideal X).
Proof.
  apply/equivP; first exact/bigfcupP.
  by apply/exists2_equiv=> y; rewrite ?andbT ?pidealE.
Qed.  

Lemma dw_closedP X : 
  reflect (dw_closed (mem X)) (dw_closedb X).
Proof. 
  apply/equivP; first apply/(fset_forallP); split.
  - move=> inX x y le_xy Xy. 
    by apply/inX/fin_idealP; exists y.
  by move=> dwX x /fin_idealP [y] /dwX; apply.
Qed.

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

(* TODO: better naming convention *)
Module Export AuxTheory.
Section AuxTheory.
Context {T U V : dwFinPOrderType}.
Implicit Types (f : T -> U) (g : U -> V).

Lemma homo_pidealE {T1 U1 : dwFinPOrderType} (f : T1 -> U1) : 
  (* TODO: reformulate in terms of dw_surjective *)
  homo_pideal f <-> (forall x y, y <= f x -> exists2 z, y = f z & z <= x).
Proof. 
  split=> [homf x y | subs].
  - rewrite -pidealE=> yin. 
    move: (homf x)=> /fsubsetP /(_ y yin). 
    move=> /imfsetP=> [[]] z /= + ->.
    by rewrite pidealE; exists z.
  move=> x; apply/fsubsetP=> y.
  rewrite pidealE=> yle.
  move: (subs x y yle)=> [z] -> zle.
  apply/imfsetP; exists z=> //=.
  by rewrite pidealE.
Qed.

Lemma homo_pideal_comp g f : 
  homo_pideal g -> homo_pideal f -> homo_pideal (g \o f).
Proof. 
  rewrite !homo_pidealE=> hg hf x y /=.
  move=> /hg [a] -> /hf [b] -> ?. 
  by exists b.
Qed.

Lemma dw_closedb_imfsetE f X : {mono f : x y / x <= y} -> dw_surjective f -> 
  dw_closedb (f @` X) = dw_closedb X.
Proof. 
  move=> /[dup] /inc_inj finj femb fdw. 
  move: (imfset_preim_eq X finj)=> /eq_dw_closed dw_preim. 
  apply/idP/idP=> /dw_closedP dw; apply/dw_closedP.
  - apply/dw_preim/dw_closed_preim=> //; exact/mono2W.
  apply/(dw_surj_closed _ fdw)=> //. 
  - exact/mono2aW.
  - by move=> x /imfsetP [y] /= _ ->; exists y.
  exact/dw_preim.
Qed.   

End AuxTheory.
End AuxTheory.

End DwFinPOrder.

Export DwFinPOrder.Exports.
Export DwFinPOrder.Def.
Export DwFinPOrder.Theory.
Export DwFinPOrder.AuxTheory.
