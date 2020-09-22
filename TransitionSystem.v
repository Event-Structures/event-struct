From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order.
From mathcomp Require Import eqtype fingraph path. 
From event_struct Require Import utilities EventStructure.
From Coq Require Import Arith.

Section transition_system.
Context {val : eqType} {dv : val}.
Notation exec_event_struct := (@exec_event_struct val).
Notation cexec_event_struct := (@cexec_event_struct val).
Implicit Types (x : var) (a : val) (t : tid).
Notation label := (@label val).
Notation n := (@n val).


(* Section with definitions for execution graph with added event *)
Section adding_event.
Variable 
  (l : label)               (* label of an event which we want to add      *)
  (e : exec_event_struct)     (* execution graph in which we want to add l *)
  (ipred : option 'I_(n e)). (* pred-child of new event (if it exists)        *)

Notation N      := (n e).
Notation lab    := (lab e).
Notation fpred  := (fpred e).
Notation frf    := (frf e).


Definition add_lab : 'I_N.+1 -> label := fun '(@Ordinal _ n L) =>
  if N =P n is ReflectF p then lab (Ordinal (ltS_neq_lt L p)) else l.

(* add_lab correctness first lemma *)
Lemma add_lab_eq_nat (m : 'I_N) (n : 'I_N.+1):
  n = m :> nat -> add_lab n = lab m.
Proof.
case: n. case: m => ? L ??/=. case: eqP=> *; last by apply/congr1/ord_inj.
exfalso. move: L. slia.
Qed.


Definition add_pred (m : 'I_N.+1) : option 'I_m := 
  let '(Ordinal m' L) := m in 
  match N =P m' with
  | ReflectT eq => let 'erefl := eq in ipred
  | ReflectF p => (fpred (Ordinal (ltS_neq_lt L p))) 
  end.

(* if l \in 'I_N.+1 and l <> N then we can convert it's type to 'I_N *)
Definition decr_ord (l : 'I_N.+1) (neq : N <> l) : 'I_N :=
  Ordinal (ltS_neq_lt (ltn_ord l) neq).

Lemma decr_ord_ord k p: (decr_ord k p) = k :> nat.
Proof. by case: k p. Qed.

(* auxiliary lemma  *)
Lemma advance_is_read {m : 'I_N} : 
  ocompatible (ext lab m)     (ext add_lab N) ->
  ocompatible (ext add_lab m) (ext add_lab N).
Proof. Admitted.

(* auxiliary lemma *)
Lemma is_read_add_lab k neq: 
  is_read (add_lab k) -> is_read (lab (decr_ord k neq)).
Proof.
have->//: add_lab k = lab (decr_ord k neq). case: k neq=> /= m ? neq.
case: eqP=> [/neq|?]//. by apply/congr1/ord_inj.
Qed.

Arguments add_lab : simpl never.

Lemma compatible_lab_decr_ord
  {k : nat} {m : nat} :
  (ocompatible (ext lab m)      (ext lab k)) ->
  (ocompatible (ext add_lab m)) (ext add_lab k).
Proof. Admitted.

Definition incr_rf_codom
  {k : 'I_N.+1} {r : 'I_N} (eq : r = k :> nat)
  (m : {l : 'I_r | (ocompatible (ext lab l)     (ext lab r))}) :
       {l : 'I_k | (ocompatible (ext add_lab l) (ext add_lab k))} :=
  let '(Ordinal r L) := r in 
  let '(Ordinal k L') := k in 
  let 'erefl := eq in
  let '(@exist _ _ o H) := m in 
  match o, H with
  | Ordinal m i, H' => 
      @exist _ _ (Ordinal i) (compatible_lab_decr_ord H')
  end. 

Lemma add_lab_N : ext add_lab N = some l.
Proof. Admitted.

Definition add_rf_some
  (m : 'I_N)
  (RF : ocompatible (ext lab m) (some l))
  (k : 'I_N.+1)
  (IR : is_read (add_lab k)) :
  {l : 'I_k | (ocompatible (ext add_lab l) (ext add_lab k))} := 
    match N =P k with
    | ReflectF p =>
      incr_rf_codom 
        (decr_ord_ord k p)
        (frf (decr_ord k p) (is_read_add_lab k p IR))
    | ReflectT eq => 
      match eq, m with
        erefl, m' => 
        @exist _ _ 
        m' 
        (advance_is_read 
          (@eq_ind_r _ _ (fun i => ocompatible _ i) RF _ add_lab_N))
      end
    end.

Lemma ord_P (k : 'I_N.+1) : N = k ->
  (~ is_read l) -> (~ is_read (add_lab k)).
Proof. Admitted.

Definition add_rf_None
  (NR : ~ is_read l)
  (k : 'I_N.+1)
  (IR : is_read (add_lab k)) :
  {l : 'I_k | (ocompatible (ext add_lab l) (ext add_lab k))} :=
  match N =P k with
  | ReflectF p =>
    incr_rf_codom 
      (decr_ord_ord k p)
      (frf (decr_ord k p) (is_read_add_lab k p IR))
  | ReflectT eq => match ord_P _ eq NR IR with end
  end.

End adding_event.


Section add_event_def.
Variables (e : exec_event_struct) (ipred : option 'I_(n e)).

Inductive add_label := 
| add_W : tid -> var -> val -> add_label
| add_R (n : 'I_(n e)) t x a : ocompatible (ext (lab e) n) (some (R t x a)) -> add_label.

Definition add_event (l : add_label) := 
  match l with
  | add_W t x a      => Pack 
                         (n e).+1 
                         (add_lab (W t x a) e)
                         (add_pred e ipred) 
                         (add_rf_None (W t x a) e ipred not_false_is_true)
  | add_R k t x a RF => Pack
                         (n e).+1 
                         (add_lab (R t x a) e)
                         (add_pred e ipred)
                         (add_rf_some (R t x a) e ipred k RF)
  end.

End add_event_def.

End transition_system.
