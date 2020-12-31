From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.
From mathcomp Require Import eqtype choice order.
Require Import Equations.Prop.Loader.

(******************************************************************************)
(* This file contains the definitions of:                                     *)
(*             wfType d == the structure for types with                       *)
(*                         well-founded partial order.                        *)
(*  well_founded_bool r <-> r is a decidable well-founded relation.           *)
(*                  wfb <-> wfType's order relation is well-founded.          *)
(*              wfb_ind <-> well-founded induction principle for wfType.      *)
(* This file also contains canonical instance of wfType for nat.              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section WfBool.

Context {T : Type} (r : rel T).

Inductive acc_bool (x : T) :=
  acc_bool_intro of (forall y : T, r y x -> acc_bool y).

Definition well_founded_bool := forall x, acc_bool x.

End WfBool.

Open Scope order_scope.

Module WellFounded.

Section ClassDef.

Record mixin_of T0 (b : Order.POrder.class_of T0)
  (T := Order.POrder.Pack tt b) := Mixin {
  _ : well_founded_bool (<%O : rel T);
}.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base   : Order.POrder.class_of T;
  mixin  : mixin_of base;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Order.POrder.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.

Definition pack :=
  fun bT b & phant_id (@Order.POrder.class disp bT) b =>
  fun m => Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @Order.POrder.Pack disp cT class.
End ClassDef.

Module Exports.

Notation wfType := type.
Coercion base : class_of >-> Order.POrder.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> Order.POrder.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Notation WfType disp T m := (@pack T disp _ _ id m).

End Exports.

End WellFounded.

Export WellFounded.Exports.


Section WfInduction.

Context {disp : unit} {T : wfType disp}.

Lemma wfb : well_founded_bool (<%O : rel T).
Proof. by case: T=> ? [] ? []. Qed.

Lemma wfb_ind (P : T -> Type) :
  (forall n, (forall m, m < n -> P m) -> P n) ->
  forall n, P n.
Proof. by move=> accP M; elim: (wfb M) => ?? /accP. Qed.

End WfInduction.

Global Instance wf_wfType {disp : unit} {T : wfType disp} :
  Equations.Prop.Classes.WellFounded (<%O : rel T).
Proof. by apply: wfb_ind; constructor. Qed.


(* Canonical well-founded order for nat *)

Import Order.NatOrder.

Lemma nat_well_founded_bool:  well_founded_bool (<%O : rel nat).
Proof. by elim/ltn_ind=> n IHn; constructor=> m /IHn. Qed.

Definition nat_wfMixin := @WellFounded.Mixin nat _ nat_well_founded_bool.
Canonical nat_wfType := Eval hnf in WfType nat_display nat nat_wfMixin.
