From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From mathcomp Require Import eqtype choice order. 

From event_struct Require Import utilities.

(******************************************************************************)
(* This file provides a theory of prime event structures.                     *)
(*       Prime.eventStruct E == the type of prime event structures.           *)
(*                              A prime event structure consists of           *)
(*                              set of events E (we require events to         *)
(*                              be equipped with decidable equality),         *)
(*                              a causality relation <= (a partial order),    *)
(*                              and a binary conflict relation # (irreflexive *)
(*                              and symmetric).                               *)
(*       Prime.eventType d   == a type of events, i.e. a type equipped with   *)
(*                              prime event structure instance.               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.LTheory.
Local Open Scope order_scope.

Declare Scope prime_eventstruct.

Local Open Scope prime_eventstruct.

Reserved Notation "x # y" (at level 75, no associativity).

Definition hereditary {T : Type} (ca cf : rel T) := 
  forall x y z : T, cf x y -> ca y z -> cf x z.

Module PrimeEventStruct.
Section ClassDef. 

Record mixin_of (T0 : Type) (b : Order.POrder.class_of T0)
                (T := Order.POrder.Pack tt b) := Mixin {
  cf : rel T; 
  _  : irreflexive cf;
  _  : symmetric cf;
  _  : hereditary (Order.POrder.le b) cf; 
}.

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

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.

Definition pack :=
  fun bT b & phant_id (@Order.POrder.class disp bT) b =>
  fun m => Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @Order.POrder.Pack disp cT class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> Order.POrder.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> Order.POrder.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.

Module Prime.
Notation eventType := type.
Notation eventStruct := class_of.
End Prime.

End Exports.

End PrimeEventStruct.

Export PrimeEventStruct.Exports.
