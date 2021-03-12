From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype choice. 
From RelationAlgebra Require Import monoid.

From event_struct Require Import utilities.

(******************************************************************************)
(* This file provides a theory of (homogeneous) monoids and partial monoids.  *)
(*                                                                            *)
(*       Monoid.m T     == a type of monoidal structures over elements        *)
(*                         of type T. Consists of binary associative          *)
(*                         operation and a neutral element (unit).            *) 
(*       Monoid.mType d == a type equipped with canonical monoidal structure. *)
(*                                                                            *)
(*       Monoid.pm d     == a type of monoidal structures with partial        *) 
(*                          operation over elements of type T.                *)
(*                          Inherits from ordinary monoidal structure.        *)
(*                          In addition, contains a orthogonality relation    *)  
(*                          which determines pairs of elements whose          *)
(*                          composition is defined.                           *) 
(*       Monoid.pmType d == a type equipped with canonical partial            *)
(*                          monoidal structure.                               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope monoid_scope.
Delimit Scope monoid_scope with monoid.

Local Open Scope monoid_scope.

Reserved Notation "\0" (at level 0).
Reserved Notation "x \+ y" (at level 40, left associativity).
Reserved Notation "x ⟂ y" (at level 20, no associativity).

Module Monoid.

Module Monoid.
Section ClassDef. 

Record mixin_of (T : Type) := Mixin {
  zero : T;
  plus : T -> T -> T;
  _    : associative plus;
  _    : left_id zero plus;
  _    : right_id zero plus;
}.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  mixin : mixin_of T;
}.
Unset Primitive Projections.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') in c.

Definition pack c := @Pack disp T c.

Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.

End ClassDef.

Module Exports.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
End Exports.

End Monoid.

Notation m     := Monoid.class_of.
Notation mType := Monoid.type.

Import Monoid.Exports.

Module Import MonoidDef.
Section MonoidDef.

Context {disp : unit} {M : mType disp}.

Definition zero : M := Monoid.zero (Monoid.class M).
Definition plus : M -> M -> M := Monoid.plus (Monoid.class M).

End MonoidDef.
End MonoidDef.

Prenex Implicits zero plus.

Module Export MonoidSyntax.
Notation "\0" := (zero) : monoid_scope.
Notation "x \+ y" := (plus x y) : monoid_scope.
End MonoidSyntax.

Module Export MonoidTheory.
Section MonoidTheory.

Context {disp : unit} {M : mType disp}.

Lemma plusA (x y z : M) : 
  x \+ y \+ z = x \+ (y \+ z). 
Proof. by case: M x y z => ? [[]]. Qed.

Lemma plus0m (x : M) : 
  \0 \+ x = x. 
Proof. by move: x; case: M=> ? [[]]. Qed.

Lemma plusm0 (x : M) : 
  x \+ \0 = x. 
Proof. by move: x; case: M=> ? [[]]. Qed.

End MonoidTheory.
End MonoidTheory.

Module PartialMonoid.
Section ClassDef. 

Record mixin_of (T0 : Type) (b : Monoid.class_of T0)
                (T := Monoid.Pack tt b) := Mixin {
  orth : rel T;
  _    : orth zero zero;
  _    : forall x, orth x zero = orth zero x;
  _    : forall x y, orth x y -> orth x zero && orth y zero;
  _    : forall x y z, orth (plus x y) z = orth x (plus y z);
}.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base  : Monoid.class_of T;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Monoid.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') in c.

Definition pack :=
  fun bE b & phant_id (@Monoid.class disp bE) b =>
  fun m => Pack disp (@Class T b m).

Definition mType := @Monoid.Pack disp cT class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> Monoid.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion mType : type >-> Monoid.type.
Canonical mType.
End Exports.

End PartialMonoid.

Notation pm     := PartialMonoid.class_of.
Notation pmType := PartialMonoid.type.

Import PartialMonoid.Exports.

Module Import PartialMonoidDef.
Section PartialMonoidDef.

Context {disp : unit} {M : pmType disp}.

Definition orth : rel M := PartialMonoid.orth (PartialMonoid.class M).

Definition valid : pred M := fun x => orth x zero.

End PartialMonoidDef.
End PartialMonoidDef.

Prenex Implicits orth valid.

Module Export PartialMonoidSyntax.
Notation "x ⟂ y" := (orth x y) : monoid_scope.
End PartialMonoidSyntax.

Module Export PartialMonoidTheory.
Section PartialMonoidTheory.

Context {disp : unit} {M : pmType disp}.

Lemma orth0 : 
  orth \0 (\0 : M). 
Proof. by case: M=> ? [? []]. Qed.

Lemma valid0 : 
  valid (\0 : M). 
Proof. by case: M=> ? [? []]. Qed.

Lemma orth_sym0 (x : M) :
  x ⟂ \0 = \0 ⟂ x.
Proof. by move: x; case: M=> ? [? []]. Qed.

Lemma orth_valid (x y : M) : 
  x ⟂ y -> valid x * valid y. 
Proof. by move: x y; case: M=> ? [? [??? H ???]] /H /andP [? ?]. Qed.

Lemma orthA (x y z : M) : 
  (x \+ y) ⟂ z = x ⟂ (y \+ z).
Proof. by move: x y z; case: M=> ? [? []]. Qed.

Lemma orth_valid_plus (x y : M) : 
  x ⟂ y = valid (x \+ y). 
Proof. by rewrite /valid -[y in LHS]plusm0 orthA. Qed.

End PartialMonoidTheory.
End PartialMonoidTheory.

End Monoid.

Export Monoid.MonoidDef.
Export Monoid.MonoidSyntax.
Export Monoid.MonoidTheory.

Export Monoid.PartialMonoidDef.
Export Monoid.PartialMonoidSyntax.
Export Monoid.PartialMonoidTheory.
