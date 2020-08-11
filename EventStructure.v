From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order eqtype div fingraph. 

Definition var := nat.

Definition ord_max {n} (i : 'I_n) : 'I_n.
case: i. case: (posnP n)=> [->//|]. by rewrite -ltn_predL=> /Ordinal. Defined.


Definition ord_of {n} (i : 'I_n) (m : nat) : 'I_n.
case: i. by case: (posnP n)=> [->//|/(ltn_pmod m)/Ordinal]. Defined.

(*Lemma ltn_modS a b: (a %% (b.+1) < b.+1)%N.
Proof. by rewrite ltn_pmod. Qed.
Definition l_mod_m {n} (l : nat) := Ordinal (ltn_modS l n).

Notation "$ n" := (l_mod_m n) (at level 0).*)

Section downward_closure.
Context {n : nat}.
Definition downward_closure (l : 'I_n) (r : rel 'I_n) := r^~ l.
Definition downward_closed (p : pred 'I_n) (r : rel 'I_n) := 
  forall x y, x \in p -> r y x -> y \in p.


Definition finite (a : pred 'I_n) :=  exists (s : seq 'I_n), forall x, x \in a -> x \in s.
Definition finite_downward_closure (r : rel 'I_n) := forall l, finite (downward_closure l r).

End downward_closure.

Section prime_event_structure.
Context {val : Type}.

(* labels for events in event structure *)
Inductive ev_label := (* + tread id *)
| R : var -> val -> ev_label
| W : var -> val -> ev_label.

Definition is_read l := exists x i, l = R x i. (* match *)
Definition is_write l := exists x i, l = W x i. (* match *)


(* labels for transitions in transition system of event structures *)
Inductive tr_label :=
| r | w : var -> val -> tr_label.


Structure evstruct := Pack {
  n                   : nat;
  E                   : 'I_n -> ev_label;
  cause               : rel 'I_n; (* --> po (k : 'I_n) : 'I_m (m < k) *)
  conflict            : rel 'I_n; (* - *)
  rf                  : 'I_n -> option 'I_n; (* ? { | } *)
  rf_codom            : forall k, reflect (is_write (E k)) (rf k == None); (* ? *)
  rf_dom              : forall k, is_read (E k) <-> (exists m, (rf k = some m) /\ is_write (E m)); (* ? *)
  rf_correct          : forall k l x i, rf k = some l -> E k = R x i -> E l = (W x i); (* ? *)
  refl_cause          : reflexive     cause;           (* -- *)
  anti_cause          : antisymmetric cause;           (* ?? *)
  trans_cause         : transitive    cause;           (* -- *)
  finite_causes_axiom : finite_downward_closure cause; (* -- *)
  confl_irrefl        : irreflexive conflict;          (* -- *)
  symm_confl          : symmetric   conflict;          (* -- *)
  consist_confl       : forall e1 e2 e3, 
                        conflict e2 e1 -> cause e1 e3 -> conflict e2 e3; (* - *)
}.

(* derive cause conflict and properties ... *)

Arguments trans_cause {_}.
Arguments confl_irrefl {_}.
Arguments consist_confl {_}.
Arguments cause {_}.
Arguments conflict {_}.
Arguments rf {_}.
Arguments E {_}.

(* event structure configuration *)
Implicit Type es : evstruct.

Notation "a # b" := (conflict a b) (at level 10).


(*Definition explicit_event (A : evstruct -> Type) (e : evstruct) (p : forall {e : evstruct}, A e)
  (_ : phantom (A e) p) := @p e.

Notation " e '|--' p " := (@explicit_event _ e _ (Phantom _ p)) (at level 0).*)


Definition explicit_event' (e : evstruct) (p : forall {e : evstruct}, rel 'I_(n e)) a b
  (_ : phantom bool (p a b)) := @p e a b.

Notation "e '|-' aRb " := (@explicit_event' e _ _ _ (Phantom _ aRb)) (at level 20).

Lemma example e a b: e |- a # b -> e |- a # b.
Proof. by []. Qed.


Lemma downward_closed_downward_closure es (l : 'I_es.(n)):
  downward_closed (downward_closure l cause) cause.
Proof.  move=> ??? /trans_cause. by apply. Qed.

Definition confl_free es (p : pred 'I_es.(n)) := forall e1 e2, e1 \in p -> e2 \in p -> ~~ (e1 # e2).
Definition config es (p : pred 'I_(n es)) :=
  (confl_free es p * downward_closed p cause)%type.

Lemma config_downward_closure es e: config es (downward_closure e cause).
Proof.
split=> [e1 e2 *|]; last by apply: downward_closed_downward_closure.
case confl: (e1 # e2)=> //=. rewrite -(confl_irrefl e).
by rewrite (consist_confl e2)// symm_confl (consist_confl e1)// symm_confl. 
Qed.

Variables (es es' : evstruct).
Implicit Types (n : 'I_(n es)) (m : 'I_(n es')).
(* transition system on event structures *)
Definition evstruct_rel lab (place : nat) (* ?seq 'I_(n es)? *) := (* exist f \in bij 'I_es'.n ?? *)
  (es.(n) = es'.(n).+1)                                                      /\
  (forall n n' m m', (eqn n m) -> (eqn n' m') -> (cause n n') -> cause m m') /\
  (forall n n' m m', (eqn n m) -> (eqn n' m') -> (n # n' = m # m'))          /\
  (forall n m, (eqn n m) -> E n = E m)                                       /\
  (forall n n' m m', (eqn n m) -> (eqn n' m') ->
    (rf n == some n') = (rf m == some m'))                                   /\
  forall m, (if lab is w x i then E (ord_max m) = W x i
   else is_read (E (ord_max m)))                                             /\
  (if place == 0 then forall n, ~~ cause m (ord_of m place)
   else forall m, (place < n es') && cause (ord_of m place) (ord_max m)).

Notation "es '-[' n , l ']-->' es' " := (evstruct_rel es es' l n) (at level 0).

End prime_event_structure.
