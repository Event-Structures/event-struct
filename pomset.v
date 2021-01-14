From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From mathcomp Require Import eqtype choice order. 
From RelationAlgebra Require Import lattice monoid rel boolean.

From event_struct Require Import utilities.

(******************************************************************************)
(* This file provides a theory of pomsets.                                    *)
(* Originally, the term pomset is an abbreviation for partially ordered       *)
(* multiset. Since then the term has been widely used in the theory of        *)
(* concurrency semantics. Here we use it following this tradition.            *)
(* That is, our pomsets are not actually multisets, but rather usual sets,    *)
(* encoded as decidable predicates.                                           *)
(*                                                                            *)
(* We inheret most of the theory from mathcomp porderType. However, in        *)
(* the pomset we additionally keep the domain on which the order is defined   *)
(* as the decidable predicate (that is, `a < b` is true iff `a` and `b`       *)
(* belong to the the domain). This simplifies the reasoning about             *) 
(* several pomset instances defined on the same type of events. For example,  *) 
(* it allows us to define combinators on pomsets (such as sum, product,       *)
(* restriction, etc) easily, keeping the same type of events for operands     *)
(* and the result of operation. It also helps us to connect the theory of     *)
(* pomsets with the theory of event structures. There we again can reuse      *)
(* the same type of events for both the event structure and its               *)
(* configurations (i.e. pomsets).                                             *)
(*                                                                            *)
(*       Pomset.eventStruct E == the type of pomset (event structures).       *)
(*                               Pomset consists of the domain (set of events *)
(*                               encoded as decidable predicate), and         *)
(*                               a causality relation <= (a partial order),   *)
(*                               such as `a < b` is false for all `a` and `b` *)
(*                               outside of the domain.                       *)
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

(* ************************************************************************** *)
(*     Cartesian product for lattice-valued functions                         *)
(* ************************************************************************** *)

Section CartesianProd.

Context {T : Type} {L : lattice.ops}.

Definition cart_prod (p q : T -> L) : T -> T -> L :=
  fun x y => p x ⊓ q y.

End CartesianProd.

Notation "p × q" := (cart_prod p q) (at level 60, no associativity) : ra_terms.

(* ************************************************************************** *)
(*     Reflexive closure for decidable relations                              *)
(* ************************************************************************** *)

(* TODO: a quick workaround to obtain "^?" notation for boolean-valued relations. 
 * A better solution would be to define in terms of kleene algebras.
 * However, the problem is that boolean-valued relations do not form KA
 * (due to lack of kleene-star, i.e. transitive closure).
 * However, to define the reflexive closure, we do not need that. 
 * Given the design of relation-algebra (see levels), it seems it would be possible 
 * in future to give a more general definition for "^?".
 *)

Section ReflexiveClosure.

Variable (T : eqType).

Definition rtc (r : rel T) : rel T := 
  fun x y => (x == y) || r x y.

End ReflexiveClosure.

Notation "r ^?" := (rtc r) (left associativity, at level 5, format "r ^?"): ra_terms.

Declare Scope pomset.
Local Open Scope pomset.

Module Pomset_.
Section ClassDef. 

Record mixin_of (E0 : Type) (* (L0 : Type) *)
                (eb : Order.POrder.class_of E0)
                (* (lb : Equality.class_of L0) *)
                (E := Order.POrder.Pack tt eb) 
                (* (L := Equality.Pack lb) *) := Mixin {
  dom : pred E;
  
  #[canonical(false)]
  bounded : (<%O) ≦ dom × dom; 
}.

Set Primitive Projections.
Record class_of (E : Type) := Class {
  base  : Order.POrder.class_of E;
  (* base2 : Equality.class_of L; *)
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Order.POrder.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (E : Type) (disp : unit) (cE : type disp).

Definition class := let: Pack _ c as cE' := cE return class_of (sort cE') in c.
Definition clone c of phant_id class c := @Pack disp E c.
Definition clone_with disp' c of phant_id class c := @Pack disp' E c.

Definition pack :=
  fun bE b & phant_id (@Order.POrder.class disp bE) b =>
  fun m => Pack disp (@Class E b m).

Definition eqType := @Equality.Pack cE class.
Definition choiceType := @Choice.Pack cE class.
Definition porderType := @Order.POrder.Pack disp cE class.
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

Notation eventType := type.
Notation eventStruct := class_of.

End Pomset_.

Export Pomset_.Exports.

Section PomsetDef.

Variable (disp : unit) (E : Pomset_.type disp).

Definition dom : pred E := Pomset_.dom (Pomset_.class E).

End PomsetDef.

Prenex Implicits dom.

Module Import PomsetSyntax.

End PomsetSyntax.

Module Import PomsetTheory.
Section PomsetTheory.

Context {disp : unit} {E : Pomset_.type disp}.

Lemma lt_dom : (<%O : rel E) ≦ dom × dom.
Proof. exact: Pomset_.bounded. Qed.

Lemma le_dom : (<=%O : rel E) ≦ (dom × dom)^?.
Proof.
  move=> x y //=. rewrite /le_bool /rtc le_eqVlt.
  move=> /orP [eq | lt]; apply /orP.
  - by left.
  by right; apply: lt_dom. 
Qed.

End PomsetTheory.
End PomsetTheory.

Module Pomset.
Notation eventType := Pomset_.eventType.
Notation eventStruct := Pomset_.eventStruct.
End Pomset.
