From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order eqtype div fingraph. 
From RelationAlgebra Require Import rel fhrel.

Definition var := nat.
Definition tread_id := seq bool.



Definition ord_of {n} (i : 'I_n) (m : nat) : 'I_n.
case: i. by case: (posnP n)=> [->|/(ltn_pmod m)/Ordinal]. Defined.

(*Lemma ltn_modS a b: (a %% (b.+1) < b.+1)%N.
Proof. by rewrite ltn_pmod. Qed.
Definition l_mod_m n (l : nat) := Ordinal (ltn_modS l n).*)

Notation "'[' l 'to' n ']'" := (ord_of n l) (at level 0).

Section downward_closure.
Context {n : nat}.
Definition downward_closure (l : 'I_n) (r : rel 'I_n) := r^~ l.
Definition downward_closed (p : pred 'I_n) (r : rel 'I_n) := 
  forall x y, x \in p -> r y x -> y \in p.


Definition finite (a : pred 'I_n) :=  exists (s : seq 'I_n), forall x, x \in a -> x \in s.
Definition finite_downward_closure (r : rel 'I_n) := forall l, finite (downward_closure l r).

End downward_closure.

Section prime_event_structure.
Context {val : eqType}.

(* labels for events in event structure *)
Inductive ev_label := (* + tread id *)
| R : tread_id -> var -> val -> ev_label
| W : tread_id -> var -> val -> ev_label.

Definition is_read  l := if l is some (R _ _ _) then true else false. 
Definition is_write l := if l is some (W _ _ _) then true else false.
Definition write_read l m := 
  match l, m with
  | some (W _ x i), some (R _ y j) => (y == x) && (i == j)
  | _, _                           => false
  end.

Definition location l := 
  match l with
  | R _ x _ | W _ x _ => x
  end.
Definition value l := 
  match l with
  | R _ _ i | W _ _ i => i
  end.
Definition tid l := 
  match l with
  | some (R t _ _) | some (W t _ _) => t | _ => [::]
  end.
Definition is_write_to x i l := if l is W _ y j then (x == y) && (i == j) else false.


(* labels for transitions in transition system of event structures *)
Inductive tr_label :=
| r : var -> val -> tr_label
| w : var -> val -> tr_label.

Definition ord_of_ex {n} {Q : 'I_n -> Prop} (k : {m : 'I_n | Q m}) :=
   match k with exist m _ => m end.


Definition sig_of_ord {T} (p : pred T) (x : T) : option {x : T | p x}.
case H : (p x); last by exact: None. by exact: some (exist _ x H). Defined.
Print simpl_rel.
Definition rel_of {T : finType} (f : T -> option T) :=
  connect [rel x y | if f y is some z then (z == x) else false].
Definition restr {n} (f : nat -> option nat) : 'I_n -> option 'I_n := 
  fun n => if f n is some m then some [m to n] else None.
Fixpoint prefix {T : eqType} (s s' : seq T) : bool :=
  match s, s with
  | [::], _            => true
  | h1 :: t1, h2 :: t2 => (h1 == h2) && (prefix t1 t2)
  | _, _               => false
  end.



Structure evstruct := Pack {
  N            : nat;
  E            : nat -> option ev_label;
  E_dom        : forall k, reflect (E k = None) (N <= k);
  po           : nat -> option nat;
  po_tid       : forall n m, po n = some m -> prefix (tid (E m)) (tid (E n));
  po_dom       : forall m, m >= N -> po m = None;
  acycl_po     : forall n k, (po n) = some k -> k < n;
  rf           : nat -> option nat;
  acycl_rf     : forall n k, (rf n) = some k -> k < n;
  rf_dom       : forall m, reflect (rf m) (is_read (E m));
  rf_codom     : forall n k, is_read (E n) -> rf n = some k -> write_read (E k) (E n);
  rf_non_confl : forall k l : 'I_N, (restr rf) k = some l -> 
   ~~[exists x, [exists y, ((rel_of (restr po)) x k)        &&      (* |   *)
                           ((rel_of (restr po)) y l)        &&      (* |   *)
                           (po x == po y) && (po x)         &&      (* | -> rf can't match two conflict events *)
                           (x != y) && (tid (E x) == tid (E y))]];  (* |   *)
}.

(* derive cause conflict and properties ... *)
Section Cause_Conflict.
Variables (e : evstruct).
Implicit Types (x : val) (i : var).
Notation N := (N e).
Notation po := (po e).
Notation E := (E e).
Notation rf := (rf e).



Section adding_event.

Variables (add_t : option 'I_N) (l : ev_label).
Hypothesis H : if add_t is some t then
                 prefix (tid (E t)) (tid (some l))
               else true.

Definition add_po : nat -> option nat := 
  fun l => if l == N then if add_t is some t then some (nat_of_ord t) else None else po l.
  
Lemma add_po_dom k : k >= N.+1 -> add_po k = None.
Proof. Admitted.

Lemma acycl_add_po k: add_po k < k.
Proof. Admitted.

Lemma add_po_tid n m : add_po n = some m -> prefix (tid (E m)) (tid (E n)). 
Proof. Admitted.

Definition radd_po := connect (rel_of (@restr N.+1 add_po)).

(* seq of all writes of (value l) to (variable x) if (is_read add_t) and [::] else *)
Definition possible_writes : seq 'I_N.+1. Admitted.
Definition add_E : nat -> option ev_label := fun t => if t == N then E t else some l.

Definition seq_of_writes := 
  if add_t is some t' then let t := [t' to (@ord_max N)] in
     [seq z <- possible_writes |
     ~~[exists x, [exists y, (radd_po x t) && (radd_po y z) &&
                             (add_po x == add_po y) && (add_po x) &&
                             (x != y) && (tid (add_E x) == tid (add_E y))]]]
  else [::].

Definition add_rf n : nat -> option nat :=
  fun l => if l == N then some n else rf l.

Fixpoint seq_of_add_rf_func (s : seq 'I_N.+1) := 
  if s is h :: t then (add_rf h) :: seq_of_add_rf_func t else [::].
Definition seq_of_add_fr := if (is_read (some l)) then seq_of_add_rf_func seq_of_writes else [:: rf].

Section add_rf_properties.
Variable (n : 'I_N.+1).
Hypothesis mem_n : n \in seq_of_writes.
Notation add_rf := (add_rf n).

Lemma acyclic_add_rf: forall k, (add_rf k) < k.
Proof. Admitted.


Lemma add_rf_dom: forall m, reflect (add_rf m) (is_read (E m)).
Proof. Admitted.

Lemma add_rf_codom: forall l k, is_read (E l) -> add_rf l = some k -> write_read (E k) (E n).
Proof. Admitted.

Lemma add_rf_non_confl : forall k l : 'I_N, (restr add_rf) k = some l -> 
   ~~[exists x, [exists y, ((rel_of (restr po)) x k)        &&      (* |   *)
                           ((rel_of (restr po)) y l)        &&      (* |   *)
                           (po x == po y) && (po x)         &&      (* | -> rf can't match two conflict events *)
                           (x != y) && (tid (E x) == tid (E y))]]   (* |   *).
Proof. Admitted.

End add_rf_properties.
End adding_event.
Notation po_res := (@restr N po).
Notation rf_res := (@restr N rf).

Definition rrf := [rel n m | if rf_res n == some m then m == n else false].
Definition cause := connect [rel m n | rrf n m || (rel_of po_res) n m].

Lemma refl_cause: reflexive cause.
Proof. by apply: connect0. Qed.

Lemma trans_cause: transitive cause.
Proof. by apply: connect_trans. Qed.

Lemma anti_cause: antisymmetric cause.
Proof.
move=> x y /andP[xy yx]. Admitted.


(*Definition pre_conflict n m := (n != m) && (tid (@E e n) == tid (@E e m)) && (@po e n == po m) && (@po e n).
Definition conflict n m := [exists x, [exists y, (cause x m) && (cause y n) && (pre_conflict x y)]].
Notation "a # b" := (conflict a b) (at level 0).


Lemma symm_conflict: symmetric conflict.
Proof. Admitted.

Lemma irrefl_conflict: irreflexive conflict.
Proof. Admitted.

Lemma consist_conflict n1 n2 n3: cause n1 n2 -> n1 # n3 -> n2 # n3.
Proof. Admitted.*)

End prime_event_structure.
