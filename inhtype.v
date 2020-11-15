From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order.
From mathcomp Require Import eqtype fingraph path. 
From event_struct Require Import utilities.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Inhabitant.

Section ClassDef.

Record mixin_of T0 (b : Equality.class_of T0) (T := Equality.Pack b) :=
  Mixin { inh : T }.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base   : Equality.class_of T;
  mixin  : mixin_of base;
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
Notation inhType := type.
Definition inh {T : inhType} : T := inh (mixin (class T)).
Notation Inhabitant T m := (@pack T _ _ id m).
Notation "[ 'inhType' 'of' T 'for' cT ]" := (@clone T cT _ id)
  (at level 0, format "[ 'inhType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'inhType' 'of' T ]" := [inhType of T for _]
  (at level 0, format "[ 'inhType'  'of'  T ]") : form_scope.
End Exports.

End Inhabitant.
Export Inhabitant.Exports.
Implicit Type T : inhType.

Section Extension.

Context {T : inhType}.
Implicit Types (x : T) (n : nat).
Notation inh := (@inh T).

Definition ext {n} (f : 'I_n -> T) : nat -> T := fun k =>
  if insub_ord n k is some k then f k else inh.

Lemma ext_add {x n} {f : 'I_n -> T} r : r != n ->
  ext (add f x) r = ext f r.
Proof.
  rewrite /ext. insub_case=> ??; insub_case=> //; try slia.
  move => L. rewrite add_lt. exact /congr1 /ord_inj.
Qed.

Lemma ext_add_n  {x n} {f : 'I_n -> T} :
  ext (add f x) n = x.
Proof. rewrite /ext. insub_case=> *; try slia. by rewrite add_ord_max. Qed.

Lemma pred_ext {n} (f : 'I_n -> T) (p : pred T) (r : 'I_n) :
 p (ext f r) = p (f r).
Proof.
  case: r=> /= *. rewrite /ext. insub_case=> [?|]; try slia.
  exact /congr1 /congr1 /ord_inj.
Qed.

Lemma rel_ext {n x} (f : 'I_n -> T) (r : rel T) (a b : nat) :
   ~ (rfield r inh) -> (r \o2 ext f) a b -> (r \o2 ext (add f x)) a b.
Proof.
  rewrite /comp2=> ?. case L: (a < n).
  { rewrite ext_add //; try slia.
    case L': (b < n). 
    { rewrite ext_add //. slia. }
    rewrite {2}/ext. insub_case=> [? _|_/(codom_rfield r)]; slia. }
  rewrite {1}/ext. insub_case=> [? _|_/(dom_rfield r)]; slia.
Qed.

End Extension.


