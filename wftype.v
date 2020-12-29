From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype.
From mathcomp Require Import eqtype fingraph path order choice. 
Require Import Equations.Prop.Loader.
From event_struct Require Import utilities.

(******************************************************************************)
(* This file contains the definitions of:                                     *)
(*       wfType d == the structure for types with well-founded partial order. *)
(*       well_founded_bool r == r is decidable well-founded relation          *)
(*       wf == the well-founded order of wfType                               *)
(*       wf_ind == well-founded induction for wfType                          *)
(* This file also contains canonical instance of wfType for nat               *) 
(******************************************************************************)

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

Lemma wf : well_founded_bool (<%O : rel T).
Proof. by case: T=> ? [] ? []. Qed.

Lemma wf_ind (P : T -> Type) :
  (forall n, (forall m, m < n -> P m) -> P n) ->
  forall n, P n.
Proof.
  move=> accP M.
  by elim: (wf M) => ?? /accP. 
Qed.

End WfInduction.

Global Instance wf_wfType {disp : unit} {T : wfType disp} : 
  Equations.Prop.Classes.WellFounded (<%O : rel T).
Proof. apply: wf_ind. by constructor. Qed.

Section NatWellFounded.

Lemma nat_well_founded_bool:  well_founded_bool (<%O : rel nat).
Proof.
  elim=> [//|n /dup ? [IHn]].
  constructor=> m; case E: (n == m)=> /= L; first by move/eqP: E=> <-.
  apply/IHn=> /=. move: L. rewrite /Order.lt /=. ssrnatlia.
Qed.

End NatWellFounded.

Import Order.NatOrder.

Definition nat_wfMixin := @WellFounded.Mixin nat _ nat_well_founded_bool.
Canonical nat_wfType := Eval hnf in WfType nat_display nat nat_wfMixin.
