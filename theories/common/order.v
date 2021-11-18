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

Module DwFinPOrder.

Module Export DwFinPOrder.
Section ClassDef. 

Record mixin_of (T0 : Type) 
                (b : Order.POrder.class_of T0)
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
