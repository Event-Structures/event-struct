From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order eqtype div fingraph choice.

Lemma ltn_modS a b: (a %% (b.+1) < b.+1)%N.
Proof. by rewrite ltn_pmod. Qed.

Definition var := nat.
Definition l_mod_m {n} (l : nat) := Ordinal (ltn_modS l n).

Notation "$ n" := (l_mod_m n) (at level 0).
Definition eq_nat {n m} {P} {Q} (k : {l: 'I_n | P l}) (m : {l: 'I_m| Q l}) :=
  match k, m with exist k _, exist m _ => eqn m k end.

Section downward_closure.
Context {T : choiceType}.
Definition downward_closure (l : T) (r : rel T) := r^~ l.
Definition downward_closed (p : pred T) (r : rel T) := 
  forall x y, x \in p -> r y x -> y \in p.


Definition finite (a : pred T) :=  exists (s : seq T), forall x, x \in a -> x \in s.
Definition finite_downward_closure (r : rel T) := forall l, finite (downward_closure l r).

End downward_closure.

Section labelDef.
Context (val : Type).

(* labels for events in event structure *)
Inductive ev_label :=
| R : var -> val -> ev_label
| W : var -> val -> ev_label.

Definition is_read l := exists x i, l = R x i.
Definition is_write l := exists x i, l = W x i.


(* labels for transitions in transition system of event structures *)
Inductive tr_label :=
| r | w : var -> val -> tr_label.
End labelDef.

Arguments R {_}.
Arguments W {_}.
Arguments is_read {_}.
Arguments is_write {_}.
Arguments w {_}.
Arguments r {_}.


Module EventStructure.

Structure mixin_of {val : Type} (T : choiceType) := Mixin {
  E                   : T -> (ev_label val);
  cause               : rel T; (* seq (T * T)%type *)
  conflict            : rel T; (* seq (T * T)%type *)
  rf                  : T -> option T;
  rf_codom            : forall k, reflect (is_write (E k)) (rf k == None);
  rf_dom              : forall k, is_read (E k) <-> (exists m, (rf k = some m) /\ is_write (E m));
  rf_correct          : forall k l x i, rf k = some l -> E k = R x i -> E l = (W x i);
  refl_cause          : reflexive     cause;
  anti_cause          : antisymmetric cause;
  trans_cause         : transitive    cause;
  finite_causes_axiom : finite_downward_closure cause;
  confl_irrefl        : irreflexive conflict;
  symm_confl          : symmetric   conflict;
  consist_confl       : forall e1 e2 e3, 
                        conflict e2 e1 -> cause e1 e3 -> conflict e2 e3;
}.

Notation class_of := mixin_of (only parsing).

Section ClassDef.
Variable (val : Type).
Structure type := Pack {sort; _ : @class_of val sort}.
Local Coercion sort : type >-> choiceType.
Variables (T : Type) (cT : type).

Definition class := let: Pack _ c := cT return @class_of val cT in c.

End ClassDef.

Arguments class {_}.

Module Exports.
Coercion sort : type >-> choiceType.
Notation eventType := type.
Notation EvMixin := Mixin.
Notation EvType T m := (@Pack T m).
End Exports.

End EventStructure.

Export EventStructure.Exports.

Section Definitions.
Context {val : Type} {T : eventType val}.
Definition E                   := EventStructure.E                   T (EventStructure.class T).
Definition cause               := EventStructure.cause               T (EventStructure.class T).
Definition conflict            := EventStructure.conflict            T (EventStructure.class T).
Definition rf                  := EventStructure.rf                  T (EventStructure.class T).
Definition rf_codom            := EventStructure.rf_codom            T (EventStructure.class T).
Definition rf_dom              := EventStructure.rf_dom              T (EventStructure.class T).
Definition rf_correct          := EventStructure.rf_correct          T (EventStructure.class T).
Definition refl_cause          := EventStructure.refl_cause          T (EventStructure.class T).
Definition anti_cause          := EventStructure.anti_cause          T (EventStructure.class T).
Definition trans_cause         := EventStructure.trans_cause         T (EventStructure.class T).
Definition finite_causes_axiom := EventStructure.finite_causes_axiom T (EventStructure.class T).
Definition confl_irrefl        := EventStructure.confl_irrefl        T (EventStructure.class T).
Definition symm_confl          := EventStructure.symm_confl          T (EventStructure.class T).
Definition consist_confl       := EventStructure.consist_confl       T (EventStructure.class T).
End Definitions.


Section nat_event_structure.
Context {val : Type}.
Notation evType := (eventType val).

(* TODO: coercion *)
Structure evstruct := Pack {
  n                    : nat;
  En                   : 'I_n.+1 -> ev_label val;
  causen               : rel 'I_n.+1; (* seq (nat * nat)%type *)
  conflictn            : rel 'I_n.+1; (* seq (nat * nat)%type *)
  rfn                  : 'I_n.+1 -> option 'I_n.+1;
  rfn_codom            : forall k, reflect (is_write (En k)) (rfn k == None);
  rfn_dom              : forall k, is_read (En k) <-> (exists m, (rfn k = some m) /\ is_write (En m));
  rfn_correct          : forall k l x i, rfn k = some l -> En k = R x i -> En l = (W x i);
  refl_causen          : reflexive     causen;
  anti_causen          : antisymmetric causen;
  trans_causen         : transitive    causen;
  finite_causes_axiomn : finite_downward_closure causen;
  confl_irrefln        : irreflexive conflictn;
  symm_confln          : symmetric   conflictn;
  consist_confln       : forall e1 e2 e3, 
                        conflictn e2 e1 -> causen e1 e3 -> conflictn e2 e3;
}.

(* event structure configuration *)

Notation "a '<=[' e ] b" := (e.(causen) a b) (at level 0).
Notation "a '#[' e ] b" := (e.(conflictn) a b) (at level 0).

(*Lemma dw_cl_dw_clo es l : downward_closed (downward_closure l es.(cause)) es.(cause).
Proof.  move=> ??? /es.(trans_cause). by apply. Qed.

Definition confl_free es (p : pred 'I_es.(n).+1) := forall e1 e2, e1 \in p -> e2 \in p -> ~~ (e1 #[es] e2).
Definition config es (p : pred 'I_es.(n).+1) :=
  (confl_free es p * downward_closed p es.(cause))%type.

Lemma config_left_clo es e: config es (downward_closure e es.(cause)).
Proof.
split=> [e1 e2 *|]; last by apply: dw_cl_dw_clo. case confl: (e1 #[es] e2)=> //=.
rewrite -(es.(confl_irrefl) e) (es.(consist_confl) e2)// es.(symm_confl).
by rewrite (es.(consist_confl) e1)// es.(symm_confl). 
Qed.

(* transition system on event structures *)
Definition evstruct_rel es es' lab (place : nat) :=
  (es.(n) = es'.(n).+1)                                              /\
  (forall n m, (n <=[es] m) -> $n <=[es'] $m)                        /\
  (forall n m, n #[es] m -> $n #[es'] $m)                            /\
  (forall n, es.(E) n = es'.(E) $n)                                  /\
  (forall k m, ((es.(rf) k) == some m) = ((es'.(rf) $k) == some $m)) /\
  (if lab is w x i then es'.(E) $(es'.(n)) = W x i
   else is_read (es'.(E) $(es'.(n))))                                /\
  (if place == 0 then forall n, ~~ n <=[es] $place
   else (place < es'.(n)) && $place <=[es] $(es'.(n))).

Notation "es '-[' n , l ']-->' es' " := (evstruct_rel es es' l n) (at level 0).*)

End nat_event_structure.
