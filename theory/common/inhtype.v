From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order.
From mathcomp Require Import eqtype fingraph path. 
From eventstruct Require Import utilities.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Inhabitant.

Section ClassDef.

Record mixin_of T0 (b : Equality.class_of T0) (T := Equality.Pack b) :=
  Mixin { inh : T }.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base   : Equality.class_of T;
  mixin  : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Equality.class_of.

Structure type := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack :=
  fun bT b & phant_id (Equality.class bT) b =>
  fun m => Pack (@Class T b m).

(* Inheritance *)
Definition eqType := @Equality.Pack cT class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> Equality.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Notation inhType := type.
Definition inh {T : inhType} : T := inh (mixin (class T)).
Notation Inhabitant T m := (@pack T _ _ id m).
Notation "[ 'inhType' 'of' T 'for' cT ]" := (@clone T cT _ id)
  (at level 0, format "[ 'inhType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'inhType' 'of' T ]" := [inhType of T for _]
  (at level 0, format "[ 'inhType'  'of'  T ]") : form_scope.
End Exports.

End Inhabitant.
Export Inhabitant.Exports.

Definition nat_inhMixin := @Inhabitant.Mixin nat _ 0.
Canonical nat_inhType := Eval hnf in Inhabitant nat nat_inhMixin.

