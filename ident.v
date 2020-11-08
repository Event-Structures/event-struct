From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.

(******************************************************************************)
(* This file contains the definitions of:                                     *)
(*   identType == interface for inhabited types with decidable equality       *)
(*                equipped with a function producing fresh values,            *)
(*                e.g. identifiers.                                           *)
(*      fresh id == a fresh identifier coming after id.                       *)
(*        ident0 == an initial identifier.                                    *)
(*      nfresh n == a sequence of size n of fresh identifiers                 *)
(*                  starting with ident0.                                     *)
(* This file also contains definitions of a Canonical identType instance for  *)
(* nat.                                                                       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module IdentType.

Section ClassDef.

Record mixin_of (T0 : Type) (b : Equality.class_of T0)
                (T := Equality.Pack b) := Mixin {
  fresh : T -> T;
  ident0 : T;
  _ : forall x n, uniq (traject fresh x n);
}.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base  : Equality.class_of T;
  mixin : mixin_of base;
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
Notation identType := type.
Definition fresh {T : identType} : T -> T := fresh (mixin (class T)).
Definition ident0 {T : identType} : T := ident0 (mixin (class T)).
Notation IdentType T m := (@pack T _ _ id m).
Notation "[ 'identType' 'of' T 'for' cT ]" := (@clone T cT _ id)
  (at level 0, format "[ 'identType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'identType' 'of' T ]" := [identType of T for _]
  (at level 0, format "[ 'identType'  'of'  T ]") : form_scope.
End Exports.

End IdentType.
Export IdentType.Exports.

Section IdentTheory.
Context {T : identType}.

Lemma uniq_traject (x : T) n : uniq (traject fresh x n).
Proof. by case: T x n=>s [b []]. Qed.

End IdentTheory.

Section Nfresh.
Context {T : identType}.

Definition nfresh (n : nat) : seq T := traject fresh ident0 n.

Lemma size_nfresh n : size (nfresh n) = n.
Proof. by rewrite /nfresh size_traject. Qed.

Lemma nfresh_uniq n : uniq (nfresh n).
Proof. exact: uniq_traject. Qed.

End Nfresh.


Section IdentDataTypes.

Definition nat_identMixin := @IdentType.Mixin _ _ succn 0 iota_uniq.
Canonical nat_identType := Eval hnf in IdentType nat nat_identMixin.

End IdentDataTypes.
