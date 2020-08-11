From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order eqtype div fingraph. 
From RelationAlgebra Require Import rel fhrel.

Definition var := nat.
Definition tread_id := nat.


(*Definition ord_max {n} (i : 'I_n) : 'I_n.
case: i. case: (posnP n)=> [->//|]. by rewrite -ltn_predL=> /Ordinal. Defined.*)


(*Definition ord_of {n} (i : 'I_n) (m : nat) : 'I_n.
case: i. by case: (posnP n)=> [->//|/(ltn_pmod m)/Ordinal]. Defined.*)

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
Context {val : eqType}.

(* labels for events in event structure *)
Inductive ev_label := (* + tread id *)
| R : tread_id -> var -> val -> ev_label
| W : tread_id -> var -> val -> ev_label.

Definition is_read  l := if l is R _ _ _ then true else false. 
Definition is_write l := if l is W _ _ _ then true else false.
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
  | R t _ _ | W t _ _ => t
  end.
Definition is_write_to x i l := if l is W _ y j then (x == y) && (i == j) else false.


(* labels for transitions in transition system of event structures *)
Inductive tr_label :=
| r : var -> val -> tr_label
| w : var -> val -> tr_label.

Definition ord_of {n} {Q : 'I_n -> Prop} (k : {m : 'I_n | Q m}) :=
   match k with exist m _ => m end.

Structure evstruct := Pack {
  n  : nat;
  E  : 'I_n -> ev_label;
  po : forall (m : 'I_n), {k : 'I_n | k < m}; (* Structure {tval : 'I_n, _ : tval < m} *)
  rf : forall k, 
  let l := E k in let x := location l in let i := value l in
  let rpo := connect [rel x y | x == ord_of (po y)] in
   is_read l -> {m : 'I_n | 
   (is_write_to x i (E m)) && (* we read frim Write *)
    ~~ (rpo k m)           && (* acyclic po with rf *)
    ~~[exists x, [exists y, (rpo x m)                        &&      (* |   *)
                            (rpo y k)                        &&      (* |   *)
                            (ord_of (po x) == ord_of (po y)) &&      (* | -> rf can't match two conflict events *)
                            (x != y) && (tid (E x) == tid (E y))]]}; (* |   *)
}.

Arguments po {_}.
Arguments rf {_}.
Arguments E  {_}.

(* derive cause conflict and properties ... *)
Section Cause_Conflict.
Variables (e : evstruct).
Implicit Type n m : 'I_(n e).

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

End Cause_Conflict.

End prime_event_structure.
