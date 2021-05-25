From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype choice. 
From RelationAlgebra Require Import monoid.
From eventstruct Require Import utils.

(******************************************************************************)
(* This file provides a theory of (homogeneous) monoids and partial monoids.  *)
(*                                                                            *)
(*       Monoid.m T     == a type of monoid structure over elements           *)
(*                         of type T. Consists of binary associative          *)
(*                         operation and a neutral element (unit).            *) 
(*       Monoid.mType d == a type equipped with canonical monoid structure.   *)
(*                                                                            *)
(*       Monoid.cm T     == a type of commutative monoid structure over       *)
(*                          elements of type T. Inherets from ordinary monoid.*)
(*       Monoid.cmType d == a type equipped with canonical structure of       *)
(*                          commutative monoid.                               *)
(*                                                                            *)
(*       Monoid.pcm d     == a type of commutative monoid structures          *)
(*                           with partial operation over elements of type T.  *)
(*                           Inherits from commutative monoid.                *)
(*                           In addition, contains a orthogonality relation   *)  
(*                           which determines pairs of elements whose         *)
(*                           composition is defined.                          *) 
(*       Monoid.pcmType d == a type equipped with canonical structure of      *)
(*                           partial commutative monoidal structure.          *)
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

Module Import Exports.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
End Exports.

Module Import Types.
Notation m     := Monoid.class_of.
Notation mType := Monoid.type.
End Types.

Module Import Def.
Section Def.

Context {disp : unit} {M : mType disp}.

Definition zero : M := Monoid.zero (Monoid.class M).
Definition plus : M -> M -> M := Monoid.plus (Monoid.class M).

End Def.
End Def.

Prenex Implicits zero plus.

Module Import Syntax.
Notation "\0" := (zero) : monoid_scope.
Notation "x \+ y" := (plus x y) : monoid_scope.
End Syntax.

Module Export Theory.
Section Theory.

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

End Theory.
End Theory.

End Monoid.

(* Unfortunately, the following Export does not achive the goal.
 * The notations `Monoid.m` and `Monoid.mType` are undefined 
 * if one imports the `monoid.v` from another file. 
 * Thus we have to resort to some copypaste.
 *)

(* Export Monoid.Types. *)
Notation m     := Monoid.class_of.
Notation mType := Monoid.type.

Export Monoid.Exports.
Export Monoid.Def.
Export Monoid.Syntax.
Export Monoid.Theory.

Module CommutativeMonoid.
Section ClassDef. 

Record mixin_of (T0 : Type) (b : Monoid.class_of T0)
                (T := Monoid.Pack tt b) := Mixin {
  _  : commutative (plus : T -> T -> T);
}.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base  : Monoid.class_of T;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion base : class_of >-> Monoid.class_of.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') in c.

Definition pack c := @Pack disp T c.

Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.

Definition as_mType := @Monoid.Pack disp cT class.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Monoid.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion as_mType : type >-> Monoid.type.
Canonical as_mType.
End Exports.

Module Import Types.
Notation cm     := CommutativeMonoid.class_of.
Notation cmType := CommutativeMonoid.type.
End Types.

Module Export Theory.
Section Theory.

Context {disp : unit} {M : cmType disp}.

Lemma plusC (x y : M) : 
  x \+ y = y \+ x. 
Proof. by case: M x y=> ? [[]] ? /= []. Qed.

End Theory.
End Theory.

End CommutativeMonoid.

(* Export CommutativeMonoid.Types. *)
Notation cm     := CommutativeMonoid.class_of.
Notation cmType := CommutativeMonoid.type.

Export CommutativeMonoid.Exports.
Export CommutativeMonoid.Theory.


Module PartialCommutativeMonoid.
Section ClassDef. 

Record mixin_of (T0 : Type) (b : CommutativeMonoid.class_of T0)
                (T := CommutativeMonoid.Pack tt b) := Mixin {
  orth : rel T;
  _    : orth zero zero;
  _    : forall x y, orth x y = orth y x;
  _    : forall x y, orth x y -> orth x zero;
  _    : forall x y z, orth (plus x y) z = orth x (plus y z);
}.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base  : CommutativeMonoid.class_of T;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> CommutativeMonoid.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') in c.

Definition pack :=
  fun bE b & phant_id (@CommutativeMonoid.class disp bE) b =>
  fun m => Pack disp (@Class T b m).

Definition as_mType := @Monoid.Pack disp cT class.
Definition as_cmType := @CommutativeMonoid.Pack disp cT class.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> CommutativeMonoid.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion as_mType : type >-> Monoid.type.
Coercion as_cmType : type >-> CommutativeMonoid.type.
Canonical as_mType.
Canonical as_cmType.
End Exports.

Module Import Types.
Notation pcm     := PartialCommutativeMonoid.class_of.
Notation pcmType := PartialCommutativeMonoid.type.
End Types.

Module Import Def.
Section Def.

Context {disp : unit} {M : pcmType disp}.

Definition orth : rel M := 
  PartialCommutativeMonoid.orth (PartialCommutativeMonoid.class M).

Definition valid : pred M := fun x => orth x zero.

End Def.
End Def.

Prenex Implicits orth valid.

Module Export Syntax.
Notation "x ⟂ y" := (orth x y) : monoid_scope.
End Syntax.

Module Export Theory.
Section Theory.

Context {disp : unit} {M : pcmType disp}.

Lemma orth0 : 
  orth \0 (\0 : M). 
Proof. by case: M=> ? [? []]. Qed.

Lemma valid0 : 
  valid (\0 : M). 
Proof. by case: M=> ? [? []]. Qed.

Lemma orth_sym (x y : M) :
  x ⟂ y = y ⟂ x.
Proof. by move: x y; case: M=> ? [? []]. Qed.

Lemma orth_valid (x y : M) : 
  x ⟂ y -> valid x * valid y. 
Proof. 
  move=> /[dup]; rewrite {2}orth_sym.
  by move: x y; case: M=> ? [? [??? H ???]] /H + /H. 
Qed.

Lemma orthA (x y z : M) : 
  (x \+ y) ⟂ z = x ⟂ (y \+ z).
Proof. by move: x y z; case: M=> ? [? []]. Qed.

Lemma orth_valid_plus (x y : M) : 
  x ⟂ y = valid (x \+ y). 
Proof. by rewrite /valid -[y in LHS]plusm0 orthA. Qed.

End Theory.
End Theory.

End PartialCommutativeMonoid.

(* Export PartialCommutativeMonoid.Types. *)
Notation pcm     := PartialCommutativeMonoid.class_of.
Notation pcmType := PartialCommutativeMonoid.type.

Export PartialCommutativeMonoid.Exports.
Export PartialCommutativeMonoid.Def.
Export PartialCommutativeMonoid.Syntax.
Export PartialCommutativeMonoid.Theory.

End Monoid.

(* TODO: do not import `Def`, `Syntax`, and `Theory` modules by default (?) *)

Export Monoid.Monoid.Exports.
Export Monoid.Monoid.Def.
Export Monoid.Monoid.Syntax.
Export Monoid.Monoid.Theory.

Export Monoid.CommutativeMonoid.Exports.
Export Monoid.CommutativeMonoid.Theory.

Export Monoid.PartialCommutativeMonoid.Exports.
Export Monoid.PartialCommutativeMonoid.Def.
Export Monoid.PartialCommutativeMonoid.Syntax.
Export Monoid.PartialCommutativeMonoid.Theory.
