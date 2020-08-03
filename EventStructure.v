From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order eqtype. 
(*Import Order.LTheory.
Open Scope order_scope.
Notation evType := (porderType tt).*)
Declare Scope hb_scope.
Delimit Scope hb_scope with G.
Open Scope hb_scope.

(*Notation sw := 
  (ltac:(let f := fresh "_top_" in let s := fresh "_s_" in move=> f s; move: f s)).*)

Definition left_clo {T : Type} (r : rel T) y := r ^~ y.


Definition finite {T : Type} (a : pred T) := 
    exists (n : nat) (f : 'I_n -> T), forall x, x \in a -> exists k, f k = x.


HB.mixin Record event_struct_of_Type T := {
  le : rel T;
  le_refl   : reflexive     le;
  le_anti   : antisymmetric le;
  le_trans  : transitive    le
}.

HB.structure Definition evstruct := { T of event_struct_of_Type T }.
Notation "a <= b" := (le a b) : hb_scope.


Section event_struct.
Context {E : evstruct.type}.
Implicit Types (p : pred E) (e : E).


Definition left_closed p := forall e1 e2, e1 \in p -> e2 <= e1 -> e2 \in p.

Lemma left_cloE e1 e2: (e2 \in left_clo le e1) = (e2 <= e1).
Proof. by []. Qed.

Lemma left_closed_left_clo e : left_closed (left_clo le e).
Proof. move=> ??? /le_trans. by apply. Qed.

End event_struct.


HB.mixin Record prime_of_event_struct E of evstruct E := 
{
    confl           : rel E;
    finite_left_clo : forall e : E, finite (left_clo le e); (***)
    confl_irrefl    : irreflexive confl;
    symm_confl      : symmetric confl;
    consist_confl   : forall e2 e1 e3 : E, (confl e1 e2) = true -> (le e2 e3) = true -> (confl e1 e3) = true; (***)
}.

HB.structure Definition prime := { T of evstruct T & prime_of_event_struct T }.
Notation "a # b" := (confl a b) (at level 0) : hb_scope.

Section prime_event_struct.
Context {E : prime.type}.
Implicit Types (p : pred E) (e : E) (s : seq E).

Definition confl_free p := forall e1 e2, e1 \in p -> e2 \in p -> ~~ (e1 # e2).
Definition config p := (confl_free p * left_closed p)%type.

Lemma config_left_clo e: config (left_clo le e).
Proof.
split=> [e1 e2 *|]; last by apply: left_closed_left_clo.
case confl: (e1 # e2)=> //=. rewrite -(confl_irrefl e).
by rewrite (consist_confl e2)// symm_confl (consist_confl e1)// symm_confl.    
Qed.

End prime_event_struct.
