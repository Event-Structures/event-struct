From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype.
From mathcomp Require Import eqtype fingraph path order tuple path. 
From event_struct Require Import utilities WfType.

Open Scope order_scope.

Definition new_axiom {T : eqType} (f : seq T -> T) := forall x, f x \notin x.

Structure mixin_of (T : eqType) := Mixin {
  new_f : seq T -> T;
  #[canonical(false)] new_ax : new_axiom new_f
}.

Structure identType := {
  sort :> wfType;
  #[canonical(false)] new_mixin : mixin_of sort
}.

Definition new {T : identType} :=  new_f T (new_mixin T).

Lemma new_not_in {T : identType} : @new_axiom T new.
Proof. rewrite /new. by case: T=> /= ? [/=]. Qed.