From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype choice. 
From RelationAlgebra Require Import monoid.
From eventstruct Require Import utils monoid.

(******************************************************************************)
(* This file provides a theory of synchronization algebras.                   *)
(*                                                                            *)
(*                                                                            *)
(*  syncalg L  == a type of synchronization algebra structures                *)
(*                over elements of type L, conventionally called labels       *) 
(*                Synchronization algebra is a partial commutative monoid     *)
(*                augumented with synchronization relation \>>, such that:    *)
(*                  a \>> b := if there exists c, s.t. a \+ c = b             *)
(*                Additionally synchronization algebra should not have no     *)
(*                non-trivial inverse elemets, that is:                       *)
(*                  x \+ y = \0 -> x = \0 && y = \0                           *)
(*                non-trivial inverses.                                       *)
(*                                                                            *)
(*  labType d == a type of labels, i.e. a type equipped with                  *)
(*               canonical synchroniazation algebra.                          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monoid_scope.

Declare Scope syncalg_scope.
Delimit Scope syncalg_scope with syncalg.

Local Open Scope syncalg_scope.

Reserved Notation "x \>> y" (at level 25, no associativity).

Module SyncAlgebra. 
Section ClassDef.

Record mixin_of (T0 : Type) (b : Monoid.PartialCommutativeMonoid.class_of T0)
                (T := Monoid.PartialCommutativeMonoid.Pack tt b) := Mixin {
  sync : rel T;
  _    : forall (x y : T), x \+ y = \0 -> x = \0; 
  _    : forall (x y : T), reflect (exists z, x \+ z = y) (sync x y); 
}.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base  : Monoid.PartialCommutativeMonoid.class_of T;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion base : class_of >-> Monoid.PartialCommutativeMonoid.class_of.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') in c.

Definition pack c := @Pack disp T c.

Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.

Definition as_mType := @Monoid.Monoid.Pack disp cT class.
Definition as_cmType := @Monoid.CommutativeMonoid.Pack disp cT class.
Definition as_pcmType := @Monoid.PartialCommutativeMonoid.Pack disp cT class.

End ClassDef. 

Module Export Exports.
Coercion base : class_of >-> Monoid.PartialCommutativeMonoid.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion as_mType : type >-> Monoid.mType.
Coercion as_cmType : type >-> Monoid.cmType.
Coercion as_pcmType : type >-> Monoid.pcmType.
Canonical as_mType.
Canonical as_cmType.
Canonical as_pcmType.
End Exports.

Module Export Types.
Notation syncalg := SyncAlgebra.class_of.
Notation labType := SyncAlgebra.type.
End Types.

Module Export Def.
Section Def.

Context {disp : unit} {L : labType disp}.

Definition sync : rel L := 
  SyncAlgebra.sync (SyncAlgebra.class L). 

End Def.
End Def.

Prenex Implicits sync.

Module Export Syntax.
Notation "x \>> y" := (sync x y) : syncalg_scope.
End Syntax.

Module Export Theory.
Section Theory.

Context {disp : unit} {L : labType disp}.

Implicit Types (x y z : L).

Lemma inverse0 x y : 
  x \+ y = \0 -> x = \0.
Proof. by move: x y; case: L=> ? [? []]. Qed.

Lemma syncP x y : 
  reflect (exists z, x \+ z = y) (sync x y). 
Proof. by move: x y; case: L=> ? [? []]. Qed.

Lemma sync0 x : 
  x \>> \0 -> x = \0. 
Proof. by move /syncP=> [] ? /inverse0. Qed.

Lemma sync_invalid x y : 
  x \>> y -> invalid x -> invalid y. 
Proof. by move /syncP=> [] z <-; exact/invalid_plus. Qed.

Lemma sync_refl x : 
  x \>> x.
Proof. by apply /syncP; exists \0; exact /plusm0. Qed.

Lemma sync_trans x y z : 
  x \>> y -> y \>> z -> x \>> z.
Proof. 
  move=> /syncP [] u <-  /syncP [] v <-.
  by apply /syncP; exists (u \+ v); rewrite plusA.
Qed.

Lemma sync_plus (x1 x2 y1 y2 : L) : 
  x1 \>> y1 -> x2 \>> y2 -> (x1 \+ x2) \>> (y1 \+ y2).
Proof. 
  move=> /syncP [] z1 <- /syncP [] z2 <-.
  apply /syncP; exists (z1 \+ z2).
  (* TODO: use some tools to deal with associativity and commutativity, 
   *   e.g. aac_rewrite library 
   *)
  rewrite !plusA.
  rewrite -[z1 \+ (x2 \+ z2)]plusA.  
  rewrite -[z1 \+ x2]plusC.  
  by rewrite !plusA.
Qed.

End Theory.
End Theory.

End SyncAlgebra.

(* Export SyncAlgebra.Types. *)
Notation syncalg := SyncAlgebra.class_of.
Notation labType := SyncAlgebra.type.

Export SyncAlgebra.Exports.
Export SyncAlgebra.Def.
Export SyncAlgebra.Syntax.
Export SyncAlgebra.Theory.

