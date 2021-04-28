From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From mathcomp Require Import eqtype choice finfun finmap tuple.
From event_struct Require Import utilities eventstructure inhtype relations.
From event_struct Require Import transitionsystem ident regmachine.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section MMConsist.

Context {V : inhType} {disp} {E : identType disp}.

(*Notation n := (@n val).*)
Notation exec_event_struct := (@fin_exec_event_struct V _ E).
Notation cexec_event_struct := (@cexec_event_struct V _ E).

Section GeneralDef.

Variable mm_pred : pred cexec_event_struct.

Inductive mm_config := MMConsist (c : config) of mm_pred (evstr c).

Coercion config_of (mmc : mm_config) :=
  let '(MMConsist c _) := mmc in c.

Canonical config_subType := [subType for config_of].

Lemma consist_inj : injective config_of.
Proof. exact: val_inj. Qed.

Variable pgm : parprog (V := V).

Definition mm_eval_ster mmc pr : seq mm_config := 
  pmap insub (eval_step pgm mmc pr).

End GeneralDef.

Export FinClosure.

End MMConsist.
