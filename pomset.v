From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From mathcomp Require Import eqtype choice order finmap. 
From RelationAlgebra Require Import lattice monoid rel boolean.

From event_struct Require Import utilities.

(******************************************************************************)
(* This file provides a theory of pomsets.                                    *)
(* Originally, the term pomset is an abbreviation for partially ordered       *)
(* multiset. Since then the term has been widely used in the theory of        *)
(* concurrency semantics. Here we use it following this tradition.            *)
(* That is, our pomsets are not actually multisets, but rather usual sets.    *)
(*                                                                            *)
(* We inheret most of the theory from mathcomp porderType.                    *)
(* We add an axiom of finite cause, that is each event has only finite prefix *)
(* of events on which it causally depends.                                    *)
(*                                                                            *)
(*       Pomset.eventStruct E == the type of pomset (event structures).       *)
(*                               Pomset consists of partial causality order   *)
(*                               (<=) which satisfies the axiom of finite     *)
(*                               cause.                                       *)
(*                               We use the name `eventStruct` to denote the  *)
(*                               pomset structure itself (as opposed to       *)
(*                               `eventType`) and for uniformity with the     *)
(*                               theory of (prime and stable) event           *)
(*                               structures.                                  *)
(*       Pomset.eventType d   == a type of events, i.e. a type equipped with  *)
(*                               pomset structure instance.                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.
Import Order.LTheory.

Local Open Scope order_scope.
Local Open Scope ra_terms.

Definition fin_cause {T : eqType} (ca : rel T) :=
  forall e, is_finite (ca^~ e).

Module Pomset.

Declare Scope pomset_scope.
Delimit Scope pomset_scope with pomset.

Local Open Scope pomset_scope.

Module Pomset.
Section ClassDef. 

Record mixin_of (T0 : Type) (b : Order.POrder.class_of T0)
                (T := Order.POrder.Pack tt b) := Mixin {
  _ : fin_cause (<=%O : rel T)
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
  fun bE b & phant_id (@Order.POrder.class disp bE) b =>
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
End Exports.

End Pomset.

Notation eventType := Pomset.type.
Notation eventStruct := Pomset.class_of.

Import Pomset.Exports.

Module Import PomsetDef.
Section PomsetDef.

Variable (disp : unit) (E : eventType disp).

(* causality alias *)
Definition ca : rel E := le.

(* strict causality alias *)
Definition sca : rel E := lt.

Definition ca_closed (X : pred E) : Prop :=
  (* ca · [X] ≦ [X] · ca; *)
  forall x y, x <= y -> X y -> X x.  

End PomsetDef.
End PomsetDef.

Prenex Implicits ca.

Module Export PomsetTheory.
Section PomsetTheory.

Context {disp : unit} {E : eventType disp}.

Lemma prefix_fin (e : E) : is_finite (<= e).
Proof. by move: e; case: E => ? [? []]. Qed.

Lemma prefix_ca_closed (e : E) : ca_closed (<= e).
Proof. move=> e1 e2 /=; exact: le_trans. Qed.

End PomsetTheory.
End PomsetTheory.

End Pomset.

Export Pomset.Pomset.Exports.
Export Pomset.PomsetDef.
Export Pomset.PomsetTheory.
