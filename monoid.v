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

Reserved Notation "x \+ y" (at level 40, left associativity).
Reserved Notation "x ⊥ y" (at level 20, no associativity).

Module Monoid.

Module Monoid.
Section ClassDef. 

Record mixin_of (T : Type) := Mixin {
  id : T;
  op : T -> T -> T;
  _  : associative op;
  _  : left_id id op;
  _  : right_id id op;
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

Definition id : M := Monoid.id (Monoid.class M).
Definition op : M -> M -> M := Monoid.op (Monoid.class M).

End MonoidDef.
End MonoidDef.

Prenex Implicits op id.

Module Export MonoidSyntax.
Notation "x \+ y" := (op x y) : monoid_scope.
End MonoidSyntax.

Module Export MonoidTheory.
Section MonoidTheory.

Context {disp : unit} {M : mType disp}.

Lemma opA (x y z : M) : 
  x \+ y \+ z = x \+ (y \+ z). 
Proof. by move: x y z; case: M=> ? [[]]. Qed.

Lemma idL (x : M) : 
  id \+ x = x. 
Proof. by move: x; case: M=> ? [[]]. Qed.

Lemma idR (x : M) : 
  x \+ id = x. 
Proof. by move: x; case: M=> ? [[]]. Qed.

End MonoidTheory.
End MonoidTheory.

Module PartialMonoid.
Section ClassDef. 

Record mixin_of (T0 : Type) (b : Monoid.class_of T0)
                (T := Monoid.Pack tt b) := Mixin {
  orth : rel T;
  _    : orth id id;
  _    : forall x, orth x id <-> orth id x;
  _    : forall x y, orth x y -> orth x id;
  _    : forall x y z, orth x y -> orth (op x y) z -> orth y z && orth x (op y z);
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

Definition valid : pred M := fun x => orth x id.

End PartialMonoidDef.
End PartialMonoidDef.

Prenex Implicits orth valid.

Module Export PartialMonoidSyntax.
Notation "x ⊥ y" := (orth x y) : monoid_scope.
End PartialMonoidSyntax.

Module Export PartialMonoidTheory.
Section PartialMonoidTheory.

Context {disp : unit} {M : pmType disp}.

Lemma orth_id : 
  orth id (id : M). 
Proof. by case: M=> ? [? []]. Qed.

Lemma valid_id : 
  valid (id : M). 
Proof. by case: M=> ? [? []]. Qed.

Lemma orth_id_sym (x : M) :
  x ⊥ id <-> id ⊥ x.
Proof. by move: x; case: M=> ? [? []]. Qed.

Lemma orthA (x y z : M) : 
  x ⊥ y -> (x \+ y) ⊥ z -> y ⊥ z && x ⊥ (y \+ z).
Proof. by move: x y z; case: M=> ? [? []]. Qed.

Lemma orth_validL (x y : M) : 
  x ⊥ y -> valid x. 
Proof. by move: x y; case: M=> ? [? []]. Qed.

Lemma orth_validR (x y : M) :
  x ⊥ y -> valid y.
Proof. 
  move=> /[dup] /orth_validL. 
  rewrite -{2}[x]idR=> /orthA /[apply].
  by move=> /andP [/orth_id_sym ?]. 
Qed.

Lemma orth_valid_op (x y : M) : 
  x ⊥ y -> valid (x \+ y). 
Proof.
  move=> /[dup] /orth_validL /orth_id_sym.
  rewrite -{2}[x]idL=> /orthA /[apply].
  by move=> /andP [? /orth_id_sym]. 
Qed.

End PartialMonoidTheory.
End PartialMonoidTheory.

End Monoid.

Export Monoid.MonoidDef.
Export Monoid.MonoidSyntax.
Export Monoid.MonoidTheory.

Export Monoid.PartialMonoidDef.
Export Monoid.PartialMonoidSyntax.
Export Monoid.PartialMonoidTheory.
