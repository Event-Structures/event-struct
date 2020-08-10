From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype eqtype div fingraph choice order.
Import Order.LTheory.
Open Scope order_scope.

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
  E        : T -> (ev_label val);
  cause    : rel T; (* seq (T * T)%type *)
  conflict : rel T; (* seq (T * T)%type *)
  rf       : T -> option T;
  _        : forall k, reflect (is_write (E k)) (rf k == None);
  _        : forall k, is_read (E k) <-> (exists m, (rf k = some m) /\ is_write (E m));
  _        : forall k l x i, rf k = some l -> E k = R x i -> E l = (W x i);
  _        : reflexive     cause;
  _        : antisymmetric cause;
  _        : transitive    cause;
  _        : finite_downward_closure cause;
  _        : irreflexive conflict;
  _        : symmetric   conflict;
  _        : forall e1 e2 e3, conflict e2 e1 -> cause e1 e3 -> conflict e2 e3;
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

Section LemmasExport.
Context {val : Type} {T : eventType val}.
Definition E := EventStructure.E T (EventStructure.class T).
Definition cause := EventStructure.cause T (EventStructure.class T).
Definition conflict := EventStructure.conflict T (EventStructure.class T).
Definition rf := EventStructure.rf T (EventStructure.class T).

Lemma trans_cause : transitive cause.
Proof. rewrite /cause. by case: T => ? []. Qed.
Lemma anti_cause : antisymmetric cause.
Proof. rewrite /cause. by case: T => ? []. Qed.
Lemma refl_cause: reflexive cause.
Proof. rewrite /cause. by case: T => ? []. Qed.
Lemma rf_codom: forall k, reflect (is_write (E k)) (rf k == None).
Proof. rewrite /E/rf. by case: T => ? []. Qed.
Lemma rf_dom: forall k, is_read (E k) <-> (exists m, (rf k = some m) /\ is_write (E m)).
Proof. rewrite /E/rf. by case: T => ? []. Qed.
Lemma rf_correct: forall k l x i, rf k = some l -> E k = R x i -> E l = (W x i).
Proof. rewrite /E/rf. by case: T => ? []. Qed.
Lemma finite_causes_axiom: finite_downward_closure cause.
Proof. rewrite /cause. by case: T => ? []. Qed.
Lemma confl_irrefl: irreflexive conflict.
Proof. rewrite /conflict. by case: T => ? []. Qed.
Lemma symm_confl: symmetric conflict.
Proof. rewrite /conflict. by case: T=> ? []. Qed.
Lemma consist_confl: forall e1 e2 e3, conflict e2 e1 -> cause e1 e3 -> conflict e2 e3.
Proof. rewrite /conflict/cause. by case: T => ? []. Qed.
End LemmasExport.
Notation "a # b" := (conflict a b) (at level 0).

(*Section ordered.
Context {val : Type} {T : eventType val}.
Implicit Type x y z : T.

Definition lt_of_cause x y := (y != x) && (cause x y).

Lemma lt_neq_le : forall x y, lt_of_cause x y = (y != x) && (cause x y).
Proof. done. Qed.

Definition orderMixin :=
 LePOrderMixin lt_neq_le refl_cause anti_cause trans_cause.

Definition ev_display : unit.
Proof. exact: tt. Qed.

Canonical porderType := POrderType ev_display T orderMixin.

End ordered.*)

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

Arguments EvMixin {_ _}.

(* event structure configuration *)
Canonical ev_Mixin (e : evstruct) := EvMixin
  e.(En)
  e.(causen)
  e.(conflictn)
  e.(rfn)
  e.(rfn_codom)
  e.(rfn_dom)
  e.(rfn_correct)
  e.(refl_causen)
  e.(anti_causen)
  e.(trans_causen)
  e.(finite_causes_axiomn)
  e.(confl_irrefln)
  e.(symm_confln)
  e.(consist_confln).
Print EventStructure.Pack.
Canonical ev_evType e := Eval hnf in EvType _ _ (ev_Mixin e).

Notation "a '<=[' e ] b" := (e.(causen) a b) (at level 0).
Notation "a '#[' e ] b" := (e.(conflictn) a b) (at level 0).

Lemma downward_closed_downward_closure (es : evstruct) (l : 'I_es.(n).+1) :
  downward_closed (downward_closure l cause) cause.
Proof.  move=> ??? /trans_cause. by apply. Qed.

Definition confl_free es (p : pred 'I_es.(n).+1) := forall e1 e2, e1 \in p -> e2 \in p -> ~~ (e1 # e2).
Definition config es (p : pred 'I_es.(n).+1) :=
  (confl_free es p * downward_closed p cause)%type.

Lemma config_downward_closure es e: config es (downward_closure e cause).
Proof.
split=> [e1 e2 *|]; last by apply: downward_closed_downward_closure.
case confl: (e1 # e2)=> //=. rewrite -(confl_irrefl e).
by rewrite (consist_confl e2)// symm_confl (consist_confl e1)// symm_confl. 
Qed.

(* transition system on event structures *)
Definition evstruct_rel es es' lab (place : nat) :=
  (es.(n) = es'.(n).+1)                                                /\
  (forall n m, (n <=[es] m) -> $n <=[es'] $m)                          /\
  (forall n m, n #[es] m -> $n #[es'] $m)                              /\
  (forall n, es.(En) n = es'.(En) $n)                                  /\
  (forall k m, ((es.(rfn) k) == some m) = ((es'.(rfn) $k) == some $m)) /\
  (if lab is w x i then es'.(En) $(es'.(n)) = W x i
   else is_read (es'.(En) $(es'.(n))))                                 /\
  (if place == 0 then forall n, ~~ n <=[es] $place
   else (place < es'.(n)) && $place <=[es] $(es'.(n))).

Notation "es '-[' n , l ']-->' es' " := (evstruct_rel es es' l n) (at level 0).

(* with caconical structure *)
Lemma foo (es es' : evstruct) (l : 'I_es.(n).+1) (m : 'I_es'.(n).+1):
  l # l -> m # m.
Proof. by rewrite !confl_irrefl. Qed.

(* without caconical structure *)
Lemma foo' (es es' : evstruct) (l : 'I_es.(n).+1) (m : 'I_es'.(n).+1):
  l #[es] l -> m #[es'] m.
Proof. by rewrite es.(confl_irrefln) es'.(confl_irrefln). Qed.

End nat_event_structure.
