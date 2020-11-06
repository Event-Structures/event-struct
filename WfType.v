From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype.
From mathcomp Require Import eqtype fingraph path order. 
From event_struct Require Import utilities.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.LTheory.
Open Scope order_scope.

Notation ordType := (orderType tt).

Section WfDef.

Context {T : Type} (r : rel T).

Inductive acc_bool (x : T) :=
  acc_bool_intro of (forall y : T, r y x -> acc_bool y).

Definition well_founded_bool := forall x, acc_bool x.

End WfDef.

Module WellFounded.

Section ClassDef.

Definition mixin_of T0 (b : Order.POrder.class_of T0) (T := Order.POrder.Pack tt b) :=
  well_founded_bool (<%O : rel T).

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base  : Order.POrder.class_of T;
  mixin : mixin_of base;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Order.POrder.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition porderType := @Order.POrder.Pack disp cT class.

End ClassDef.

Coercion base : class_of >-> Order.POrder.class_of.
Coercion sort : type >-> Sortclass.
Coercion porderType : type >-> Order.POrder.type.
Canonical porderType.

End WellFounded.

Notation wfType := (WellFounded.type tt).

Import WellFounded.

Section WfInduction.

Context {T : wfType}.

Lemma wf : well_founded_bool (<%O : rel T).
Proof. by case: T=> ? []. Qed.

Lemma wf_ind (P : T -> Type) :
  (forall n, (forall m, m < n -> P m) -> P n) ->
  forall n, P n.
Proof. move=> accP M. by elim: (wf M) => ?? /accP. Qed.

End  WfInduction.
