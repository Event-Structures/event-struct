From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order eqtype. 

(*
1) event structure
2) ev_label
3) Relation
*)

Definition var := nat.

Definition refl_trans_closure : rel nat -> rel nat. admit. Admitted.
Definition downward_closure (n : nat) (r : rel nat) := r^~ n.

Definition finite (a : pred nat) :=  exists (s : seq nat), forall x, x \in a -> x \in s.
Definition finite_causes_axiom (n : nat) (r : rel nat) := finite (downward_closure n r).


Section prime_event_structure.
Context {val : Type}.

(* labels for events in event structure *)
Inductive ev_label :=
| R : var -> val -> ev_label
| W : var -> val -> ev_label.

(* labels for transitions in transition system of event structures *)
Inductive tr_label :=
| r | w : var -> val -> tr_label.

Structure evstruct := Pack {
  n               : nat;
  E               : 'I_n -> ev_label;
  cause           : rel nat; (* seq (nat * nat)%type *)
  conflict        : rel nat; (* seq (nat * nat)%type *)
  rf              : {n : 'I_n | exists x i, E n = R x i} ->
                    {n : 'I_n | exists x i, E n = W x i}; (* need coercion *)
  refl_cause      : reflexive     cause;
  anti_cause      : antisymmetric cause;
  trans_cause     : transitive    cause;
  confl_irrefl    : irreflexive conflict;
  symm_confl      : symmetric conflict;
  consist_confl   : forall e1 e2 e3, 
                      conflict e1 e2 -> cause e2 e3 -> conflict e1 e3;
}.

Implicit Type es : evstruct.

Reserved Notation "a '--' l '-->' b" (at level 0).

(*Definition evstruct_step {val : Type} (es es' : evstruct) (m : nat) (l : tr_label) :=
  ((es.(n) = es'.(n).+1)                          /\
  (forall n m, es.(cause) n m -> es'.(cause) n m) /\
  (forall n m, es.(conflict) -> es'.(conflict))   /\
  (forall (n : ),)
  *)
  
End prime_event_structure.