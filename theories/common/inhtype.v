From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order.
From mathcomp Require Import eqtype choice fingraph path. 
From eventstruct Require Import utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* TODO: add scope? *)
Notation "?| T |" := (inhabited T)
  (at level 0, T at level 99, format "?| T |").

(* TODO: add scope? *)
Notation "??| A |" := (~~ pred0b A)
  (at level 0, A at level 99, format "??| A |").

Section Theory.
Implicit Types (aT rT : Type) (fT : finType).

Lemma nihn_inh_fun aT rT : 
  ~ ?|aT| -> ?|aT -> rT|.
Proof. 
  move=> H; constructor. 
  have fT: (forall x : aT, False).
  - move=> x; apply/H; constructor; exact/x. 
  by refine (fun x => match fT x with end).
Qed.

Lemma inh_impl aT rT : 
  (aT -> rT) -> ?|aT| -> ?|rT|.
Proof. move=> f [x]; exists; exact/(f x). Qed.

Lemma inh_iff aT rT : 
  (aT -> rT) -> (rT -> aT) -> ?|aT| <-> ?|rT|.
Proof. by move=> f g; split; apply/inh_impl. Qed.

Lemma fin_inhP fT : 
  reflect ?|fT| ??|fT|.
Proof. 
  apply/(equivP pred0Pn). 
  split; move=> [] //. 
  by move=> x; exists x.
Qed.

Lemma sub_fin_inhP fT (P : pred fT) (S : subType P) : 
  reflect ?|S| ??|P|.
Proof. 
  apply/(equivP pred0Pn). 
  split=> [[x Px] | [x]] //. 
  - exists; exact/(Sub x Px). 
  exists (val x); exact/(valP x).
Qed.


Variables (T : Type) (R : T -> T -> Type) (r : rel T).
Hypothesis (InhP : forall x y, reflect ?|R x y| (r x y)).
Hypothesis (Refl : forall x, R x x).
Hypothesis (Trans : forall x y z, R x y -> R y z -> R x z).

Lemma is_inh_refl : reflexive r. 
Proof. move=> ?; apply/InhP; exists; exact/Refl. Qed.
  
Lemma is_inh_trans : transitive r. 
Proof. move=> ??? /InhP[A] /InhP[B]; apply/InhP; exists; exact/(Trans A B). Qed.

End Theory.


Module Inhabited.

Section ClassDef.

Record mixin_of T0 (b : Choice.class_of T0) 
                   (T := Choice.Pack b) := Mixin { 
  inh : T 
}.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base   : Choice.class_of T;
  mixin  : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Choice.class_of.

Structure type := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack :=
  fun bT b & phant_id (Choice.class bT) b =>
  fun m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Canonical eqType.
Canonical choiceType.
Notation inhType := type.
Definition inh {T : inhType} : T := inh (mixin (class T)).
Notation Inhabited T m := (@pack T _ _ id m).
Notation "[ 'inhType' 'of' T 'for' cT ]" := (@clone T cT _ id)
  (at level 0, format "[ 'inhType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'inhType' 'of' T ]" := [inhType of T for _]
  (at level 0, format "[ 'inhType'  'of'  T ]") : form_scope.
End Exports.

End Inhabited.

Export Inhabited.Exports.

Definition nat_inhMixin := @Inhabited.Mixin nat _ 0.
Canonical nat_inhType := Eval hnf in Inhabited nat nat_inhMixin.
