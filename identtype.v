From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype.
From mathcomp Require Import eqtype fingraph path order tuple path. 
From event_struct Require Import utilities.

Section ClassDef.

Definition freshness_axiom {T : eqType} (f : seq T -> T) := 
  forall x, f x \notin x.

Structure mixin_of (T : eqType) := Mixin {
  fresh : seq T -> T;
  #[canonical(false)] freshness : freshness_axiom fresh
}.

Structure identType := {
  sort :> eqType;
  #[canonical(false)] fresh_mixin : mixin_of sort
}.

End ClassDef.

Section Exports.

Notation fresh := (fresh _ (fresh_mixin _)).

Lemma fresh_not_in {T : identType} : @freshness_axiom T fresh.
Proof. rewrite /fresh. by case: T=> /= ? [/=]. Qed.

End Exports.