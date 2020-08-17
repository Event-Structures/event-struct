From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order eqtype div fingraph. 
From Equations Require Import Equations.
From event_struct Require Import ssrlia.
Definition var := nat.
Definition tread_id := nat.



Section prime_event_structure.
Context {val : eqType}.

(* labels for events in event structure *)
Inductive label := (* + tread id *)
| R : tread_id -> var -> val -> label
| W : tread_id -> var -> val -> label.

Definition is_read  l := if l is (R _ _ _) then true else false.

Definition is_write l := if l is (W _ _ _) then true else false.

Definition read_from l m := 
  match l, m with
  | (W _ x i), (R _ y j) => (y == x) && (i == j)
  | _, _                 => false
  end.

Definition tid l := 
  match l with
  |  (R t _ _) | (W t _ _) => t
  end.

Structure execgraph := Pack {
  n  : nat;
  E  : 'I_n -> label;
  po : forall (m : 'I_n), {? k : 'I_n | k < m}; (* Structure {tval : 'I_n, _ : tval < m} *)
  rf : forall k : {l : 'I_n | is_read (E l)},
                  {l : 'I_n | (l < sval k) && (read_from (E l) (E (sval k)))};
  (*rf_consit    : forall k,
                let rpo := connect [rel x y | if (po y) is some z then sval z == y else false] in
                 ~~[exists x, [exists y, 
                 (rpo x (sval k)) && (rpo y (sval (rf k))) &&
                 (foo_eq (po x) (po y)) &&  (x != y) && (tid (E x) == tid (E y))]];*)
}.

Equations equal (n m : nat) : { n = m } + { n <> m } :=
equal O O := left erefl ;
equal (S n) (S m) with equal n m := {
  equal (S n) (S ?(n)) (left erefl) := left erefl ;
  equal (S n) (S m) (right p) := right _ } ;
equal x y := right _.

Lemma ltS_neq_lt {n N}: n < N.+1 -> N <> n -> n < N.
Proof. ssrnatlia. Qed. 

Section adding_event.
Variable (lab : label) (e : execgraph) (pre_po : option 'I_(n e)).
Notation N := (n e).
Notation E := (E e).
Notation po := (po e).
Notation rf := (rf e).


Equations add_E (n : 'I_N.+1) : label :=
add_E (@Ordinal n L) with equal N n := {
  add_E _ (left erefl) := lab;
  add_E (Ordinal L) (right p) := E (Ordinal (ltS_neq_lt L p))
}.

Equations incr_ord (m : 'I_N) : 'I_N.+1 :=
incr_ord (@Ordinal n L) := @Ordinal _ n (ltn_trans L (ltnSn _)).

Lemma add_E_incr_ord m : E m = add_E (incr_ord m).
Proof.
funelim (incr_ord m). funelim (add_E (Ordinal (ltn_trans i (ltnSn N)))). 
- exfalso. case: eqargs=> E. move: E i0=>->. ssrnatlia.
case: eqargs=> EQ. by apply/congr1/ord_inj.
Qed.

Lemma ltnnn {n}: ~ (n < n).
Proof. ssrnatlia. Qed.


Lemma incr_is_read {m} {L} L' : read_from (E m)                (add_E (@Ordinal _ N L)) ->
                                read_from (add_E (incr_ord m)) (add_E (@Ordinal _ N L')).
Proof.
rewrite add_E_incr_ord. have->//: (add_E (Ordinal L)) = (add_E (Ordinal L')).
by apply/congr1/ord_inj.
Qed.

Equations incr_oord (n : option 'I_N) : option 'I_N.+1 :=
incr_oord (some (Ordinal L)) := some (Ordinal (ltn_trans L (ltnSn N)));
incr_oord None := None.

Lemma nltn0 n: ~ (n < 0).
Proof. ssrnatlia. Qed.

Equations nat_osig_to_ord {m : 'I_N} (k : {? k : 'I_N | k < m}) : {? k : 'I_N.+1 | k < m} :=
nat_osig_to_ord (some (@exist _ _ (Ordinal L) L')) :=  some (@exist _ _ (Ordinal (ltn_trans L (ltnSn _))) L');
nat_osig_to_ord None := None.


Equations add_po (pre_n : option 'I_N) (n : 'I_N.+1) : {? k : 'I_N.+1 | k < n} :=
add_po on (@Ordinal _ n L) with equal N n := {
  add_po None _ (left erefl) := None;
  add_po (some (Ordinal L')) (Ordinal L) (left erefl) :=
    some (@exist _ _ (Ordinal (ltn_trans L' (ltnSn _))) L');
  add_po _ (Ordinal L) (right p) := nat_osig_to_ord (po (Ordinal (ltS_neq_lt L p)))
}.

Lemma and_i {a b : bool} : a -> b -> a && b.
Proof. by move=>->. Qed.

Equations decr_ord (l : 'I_N.+1) (neq : N <> l) : 'I_N :=
decr_ord (Ordinal L) neq := Ordinal (ltS_neq_lt L neq).

Lemma is_read_add_E_E l neq: is_read (add_E l) -> is_read (E (decr_ord l neq)).
Proof.
have->//: add_E l = E (decr_ord l neq). funelim (add_E l); first by case: neq.
simp decr_ord. by apply/congr1/ord_inj.
Qed.

Equations decr_rf_dom (k : {l : 'I_N.+1 | is_read (add_E l)}) (neq : N <> (sval k)) : 
                           {l : 'I_N | is_read (E l)} :=
decr_rf_dom (@exist (Ordinal L) IR) neq :=
  @exist _ _ (Ordinal (ltS_neq_lt L neq)) (is_read_add_E_E _ neq IR).

Lemma and_e1 {a b}: a && b -> a.
Proof. by case: a. Qed.

Lemma and_e2 {a b}: a && b -> b.
Proof. by case: a. Qed.

Lemma nat_of_incr_od (l : 'I_N) : (incr_ord l) = l :> nat.
Proof. by funelim (incr_ord l). Qed.

Lemma incr_ord_le {l r : 'I_N}: l < r -> incr_ord l < incr_ord r.
Proof. by rewrite !nat_of_incr_od. Qed.

Lemma read_from_incr_ord {l r : 'I_N}: read_from (E l) (E r) ->
  read_from (add_E (incr_ord l)) (add_E (incr_ord r)).
Proof. by rewrite !add_E_incr_ord. Qed.

Equations incr_rf_codom 
 (k : {l : 'I_N.+1 | is_read (add_E l)})
 (r : {l : 'I_N | is_read (E l)}) (eq : incr_ord (sval r) = sval k)
 (m : {l : 'I_N    | (l < (sval r)) && (read_from (E l)     (E     (sval r)))}) :
      {l : 'I_N.+1 | (l < sval k) && (read_from (add_E l) (add_E (sval k)))} :=
incr_rf_codom (@exist _ _) _ erefl (@exist l COND) :=
  @exist _ _ (incr_ord l) (and_i (incr_ord_le (and_e1 COND)) (read_from_incr_ord (and_e2 COND))).


Lemma sval_decr_ord (k : {l : 'I_N.+1 | is_read (add_E l)}) :
  forall p, incr_ord (sval (decr_rf_dom k p)) = sval k.
Proof.
case: k=> [[*]]. simp decr_rf_dom=>/=. simp incr_ord. by apply/ord_inj.
Qed.

Equations add_rf_some
  (m : 'I_N) (RF : read_from (E m) (add_E ord_max))
  (k : {l : 'I_N.+1 | is_read (add_E l)}) :
       {l : 'I_N.+1 | (l < sval k) && (read_from (add_E l) (add_E (sval k)))} :=
add_rf_some _ _ k with equal N (sval k) := {
  add_rf_some (Ordinal m_le_N) RF (@exist (Ordinal L) _) (left erefl) :=
    (@exist _ _ (incr_ord (Ordinal m_le_N)) (and_i m_le_N (incr_is_read L RF)));
  add_rf_some _ _ k (right p) :=  incr_rf_codom k _ (sval_decr_ord _ _) (rf (decr_rf_dom k p))
}.

Lemma ord_P {L} : (~ is_read (add_E ord_max)) -> (~ is_read (add_E (@Ordinal N.+1 N L))).
Proof. have->//: ord_max = (@Ordinal N.+1 N L). by apply/ord_inj. Qed.


Equations add_rf_None
  (NR : ~ is_read (add_E ord_max))
  (k : {l : 'I_N.+1 | is_read (add_E l)}) :
       {l : 'I_N.+1 | (l < sval k) && (read_from (add_E l) (add_E (sval k)))} :=
add_rf_None _ k with equal N (sval k) := {
  add_rf_None NR (@exist (Ordinal L) IR) (left erefl) with (ord_P NR) IR := {};
  add_rf_None _ k (right p) :=  incr_rf_codom k _ (sval_decr_ord _ _) (rf (decr_rf_dom k p))
}.

End adding_event.
(* derive cause conflict and properties ... *)
Section Cause_Conflict.
Variables (e : execgraph) (lab : label).

Notation N := (n e).
Notation E := (E e).
Notation po := (po e).
Notation rf := (rf e).

Definition rpo := connect [rel x y | if (po x) is some z then sval z == y else false].

Definition case_bool b : {b = true} + {b = false} := if b then left erefl else right erefl.

Definition rrf (n m : 'I_N) : bool := 
  if case_bool (is_read (E n)) is (left IT) 
    then sval (rf (@exist _ _ n IT)) == m
  else false.

Definition cause := connect [rel n m | rrf n m || rpo n m].

Lemma refl_cause: reflexive cause.
Proof. exact: connect0. Qed.

Lemma trans_cause: transitive cause.
Proof. exact: connect_trans. Qed.

Lemma anti_cause: antisymmetric cause.
Proof.
move=> x y /andP[xy yx]. Admitted.


(*Definition pre_conflict n m := (n != m) && (tid (E n) == tid (E m)) && (ord_of (po n) == ord_of (po m)).
Definition conflict n m := [exists x, [exists y, (cause x m) && (cause y n) && (pre_conflict x y)]].
Notation "a # b" := (conflict a b) (at level 0).


Lemma symm_conflict: symmetric conflict.
Proof. Admitted.

Lemma irrefl_conflict: irreflexive conflict.
Proof. Admitted.


Lemma consist_conflict n1 n2 n3: cause n1 n2 -> n1 # n3 -> n2 # n3.
Proof. Admitted.*)

End Cause_Conflict.

End prime_event_structure.
