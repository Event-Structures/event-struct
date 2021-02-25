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
(*                          In addition, contains a binary validity relation  *)  
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
Reserved Notation "x \+? y" (at level 20, no associativity).

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

Notation class_of := mixin_of (only parsing). 

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') in c.

Definition pack c := @Pack disp T c.

Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
End Exports.

End Monoid.

Notation m     := Monoid.mixin_of.
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
Proof. by move: x y z; case: M=> ? []. Qed.

Lemma idL (x : M) : 
  id \+ x = x. 
Proof. by move: x; case: M=> ? []. Qed.

Lemma idR (x : M) : 
  x \+ id = x. 
Proof. by move: x; case: M=> ? []. Qed.

End MonoidTheory.
End MonoidTheory.

End Monoid.

Export Monoid.MonoidDef.
Export Monoid.MonoidSyntax.
Export Monoid.MonoidTheory.
