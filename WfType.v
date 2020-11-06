From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype.
From mathcomp Require Import eqtype fingraph path order. 
From event_struct Require Import utilities.

Import Order.TTheory.
Open Scope order_scope.

Notation ordType := (orderType tt).

Section WfDef.

Variable T : ordType.

Inductive acc (x : T) :=
  acc_intro of (forall y : T, y < x -> acc y).

Definition well_founded := forall x, acc x.

End WfDef.

Structure wfType : Type := 
  Well_founded {type :> ordType; #[canonical(false)] wf : well_founded type}.

Section WfInduction.

Context {T : wfType}.

Lemma wf_ind (P : T -> Type) :
  (forall n, (forall m, m < n -> P m) -> P n) ->
  forall n, P n.
Proof. move=> accP M. by elim: (wf _ M) => ?? /accP. Qed.

End  WfInduction.
