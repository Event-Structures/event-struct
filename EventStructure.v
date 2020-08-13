From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order eqtype div fingraph. 
From Equations Require Import Equations.
From event_struct Require Import ssrlia.
Definition var := nat.
Definition tread_id := nat.


(*Definition ord_max {n} (i : 'I_n) : 'I_n.
case: i. case: (posnP n)=> [->//|]. by rewrite -ltn_predL=> /Ordinal. Defined.*)


(*Definition ord_of {n} (i : 'I_n) (m : nat) : 'I_n.
case: i. by case: (posnP n)=> [->//|/(ltn_pmod m)/Ordinal]. Defined.*)


Section prime_event_structure.
Context {val : eqType}.

(* labels for events in event structure *)
Inductive ev_label := (* + tread id *)
| R : tread_id -> var -> val -> ev_label
| W : tread_id -> var -> val -> ev_label.

Definition is_read  l := if l is (R _ _ _) then true else false. 
Definition is_write l := if l is (W _ _ _) then true else false.
Definition write_read l m := 
  match l, m with
  | (W _ x i), (R _ y j) => (y == x) && (i == j)
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
  |  (R t _ _) | (W t _ _) => t
  end.
Definition is_write_to x i l := if l is W _ y j then (x == y) && (i == j) else false.
(*Definition foo_eq {n} {P} {Q} (x : option {l : 'I_n | P l}) (y : option {k : 'I_n | Q k}) :=
  match x, y with
  | (exist a _), (exist b _) => (a == b)
  | _, _ => false
  end.*)


(* labels for transitions in transition system of event structures *)

Structure evstruct := Pack {
  n  : nat;
  E  : 'I_n -> ev_label;
  po : forall (m : 'I_n), option {k : 'I_n | k < m}; (* Structure {tval : 'I_n, _ : tval < m} *)
  rf : forall k : {l : 'I_n | is_read (E l)},
                  {l : 'I_n | (l < proj1_sig k) && (write_read (E l) (E (proj1_sig k)))};
  (*rf_consit    : forall k,
                let rpo := connect [rel x y | if (po y) is some z then proj1_sig z == y else false] in
                 ~~[exists x, [exists y, 
                 (rpo x (proj1_sig k)) && (rpo y (proj1_sig (rf k))) &&
                 (foo_eq (po x) (po y)) &&  (x != y) && (tid (E x) == tid (E y))]];*)
}.

Arguments po {_}.
Arguments rf {_}.
Arguments E  {_}.

Equations equal (n m : nat) : { n = m } + { n <> m } :=
equal O O := left erefl ;
equal (S n) (S m) with equal n m := {
  equal (S n) (S ?(n)) (left erefl) := left erefl ;
  equal (S n) (S m) (right p) := right _ } ;
equal x y := right _.

Lemma ltS_neq_lt {n N}: n < N.+1 -> N <> n -> n < N.
Proof. ssrnatlia. Qed. 


Equations decr_ord (N : nat) (n : 'I_N.+1) : 'I_N + {n : nat | n = N} := 
decr_ord 0 n := inr (@exist _ _ 0 erefl);
decr_ord (N'.+1) (@Ordinal n L) with equal (N'.+1) n := {
  decr_ord (N'.+1) (@Ordinal ?(N'.+1) L) (left erefl) := inr (@exist _ _ N'.+1 erefl);
  decr_ord (N'.+1) (Ordinal L) (right p) := inl (Ordinal (ltS_neq_lt L p))
}.

Section adding_event.
Variable (lab : ev_label).

Equations add_E (N : nat) (f : 'I_N -> ev_label) (n : 'I_N.+1) : ev_label :=
add_E 0 f _ := lab;
add_E (N.+1) f (@Ordinal n L) with equal (N.+1) n := {
  add_E (N.+1) f (@Ordinal ?(N.+1) L) (left erefl) := lab;
  add_E (N.+1) f (@Ordinal n L) (right p) := f (Ordinal (ltS_neq_lt L p))
}.

Equations incr_oord (N : nat) (n : option 'I_N) : option 'I_N.+1 :=
incr_oord N (some (Ordinal L)) := some (Ordinal (ltn_trans L (ltnSn N)));
incr_oord N None := None.

Lemma nltn0 n: ~ (n < 0).
Proof. ssrnatlia. Qed.

Equations nat_osig_to_ord (N : nat) (m : 'I_N) (k : {? k : 'I_N | k < m}) : {? k : 'I_N.+1 | k < m} :=
nat_osig_to_ord N _ (some (@exist _ _ (Ordinal k_le_N) k_le_m)) := 
  some (@exist _ _ (Ordinal (ltn_trans k_le_N (ltnSn N))) k_le_m);
nat_osig_to_ord N _ None := None.

Equations add_po (N : nat) (f : forall (m : 'I_N), {? k : 'I_N | k < m})
                 (pre_n : option 'I_N) (n : 'I_N.+1) : {? k : 'I_N.+1 | k < n} :=
add_po 0 _ None _ := None;
add_po 0 _ (some (Ordinal F)) _ with (nltn0 _ F) := {};
add_po (N.+1) f on (@Ordinal n L) with equal (N.+1) n := {
  add_po (N.+1) f None (@Ordinal ?(N.+1) L) (left erefl) := None;
  add_po (N.+1) f (some (@Ordinal k L')) (@Ordinal ?(N.+1) L) (left erefl) :=
    some (@exist _ _ (Ordinal (ltn_trans L' (ltnSn N.+1))) L');
  add_po (N.+1) f _ (@Ordinal n L) (right p) := nat_osig_to_ord _ _ (f (Ordinal (ltS_neq_lt L p)))
}.

End adding_event.

(* derive cause conflict and properties ... *)
(*Section Cause_Conflict.
Variables (e : evstruct) (lab : ev_label).


Equations add_E {l : 'I_N.+1 | is_read (E l)}

Definition add_rf {l : 'I_N.+1 | is_read (E l)},
                  {l : 'I_N.+1 | (l < proj1_sig k) && (write_read (E l) (E (proj1_sig k)))} :=
  fun l => if proj_sig1 l == N then (exist write_place (H : write_place < proj_sig1 l) )


Definition add_po () := .


Definition pre_rpo m n := n == ord_of (po m).
Definition rpo := connect pre_rpo.

Definition rrf n m := n == ord_of (po m).
Definition cause := connect [rel n m | rrf n m || rpo n m].

Lemma irrefl_cause: irreflexive cause.
Proof. Admitted.

Lemma trans_cause: transitive cause.
Proof. Admitted.

Lemma anti_cause: antisymmetric cause.
Proof. Admitted.


Definition pre_conflict n m := (n != m) && (tid (E n) == tid (E m)) && (ord_of (po n) == ord_of (po m)).
Definition conflict n m := [exists x, [exists y, (cause x m) && (cause y n) && (pre_conflict x y)]].
Notation "a # b" := (conflict a b) (at level 0).


Lemma symm_conflict: symmetric conflict.
Proof. Admitted.

Lemma irrefl_conflict: irreflexive conflict.
Proof. Admitted.


Lemma consist_conflict n1 n2 n3: cause n1 n2 -> n1 # n3 -> n2 # n3.
Proof. Admitted.

End Cause_Conflict.*)

End prime_event_structure.
