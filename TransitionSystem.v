From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order.
From mathcomp Require Import eqtype fingraph path. 
From event_struct Require Import utilities EventStructure.
From Coq Require Import Arith.
(*Section foo.
Context {N : nat}.
Implicit Type (x y : 'I_N).
Definition lt_ord (x y : 'I_N) := (x < y)%N.

Lemma ltn_def (x y : 'I_N) : (x < y)%N = (y != x) && (x <= y)%N.
Proof. by rewrite ltn_neqAle eq_sym. Qed.

Lemma leqnn' x : (x <= x)%N.
Proof. Admitted.

Lemma anti_leq' : @antisymmetric 'I_N [eta leq].
Proof. Admitted.

Lemma leq_trans': @transitive 'I_N [eta leq].
Proof. Admitted.

Print anti_leq.

Definition orderMixin' :=
LePOrderMixin ltn_def leqnn' anti_leq' leq_trans'.

Definition ev_display' : unit.
Proof. exact: tt. Qed.

Canonical porderType := POrderType ev_display' 'I_N orderMixin'.
End foo.*)
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
  (pre_pred : option 'I_(n e)). (* pred-child of new event (if it exists)        *)
Notation N := (n e).
Notation lab := (lab e).
Notation pred := (pred e).
Notation rf := (rf e).


Definition add_lab : 'I_N.+1 -> label := fun '(@Ordinal _ n L) =>
  if N =P n is ReflectF p then lab (Ordinal (ltS_neq_lt L p)) else l.

(* add_lab correctness first lemma *)
Lemma add_lab_eq_nat (m : 'I_N) (n : 'I_N.+1):
  n = m :> nat -> add_lab n = lab m.
Proof.
case: n. case: m => ? L ??/=. case: eqP=> *; last by apply/congr1/ord_inj.
exfalso. move: L. ssrnatlia.
Qed.

(* add_lab correctness second lemma *)
Lemma add_lab_N {L : N < N.+1}: add_lab (Ordinal L) = l.
Proof. move=> /=. by case: eqP. Qed.


Definition add_pred (m : 'I_N.+1) : option 'I_m := 
  let '(Ordinal m' L) := m in 
  match N =P m' with
  | ReflectT eq => let 'erefl := eq in pre_pred
  | ReflectF p => (pred (Ordinal (ltS_neq_lt L p))) 
  end.

(* if l \in 'I_N.+1 and l <> N then we can convert it's type to 'I_N *)
Definition decr_ord (l : 'I_N.+1) (neq : N <> l) : 'I_N :=
  Ordinal (ltS_neq_lt (ltn_ord l) neq).

Lemma decr_ord_ord k p: (decr_ord k p) = k :> nat.
Proof. by case: k p. Qed.

(* auxiliary lemma  *)
Lemma advance_is_read {K: N < N.+1} {m : 'I_(Ordinal K)} {L} L' : 
  compatible (lab m)                           (add_lab (@Ordinal _ N L)) ->
  compatible (add_lab (advance (Ordinal K) m)) (add_lab (@Ordinal _ N L')).
Proof.
rewrite [add_lab (advance _ _)](add_lab_eq_nat m)//.
have->//: (add_lab (Ordinal L)) = (add_lab (Ordinal L')).
by apply/congr1/ord_inj.
Qed.

(* auxiliary lemma *)
Lemma is_read_add_lab k neq: 
  is_read (add_lab k) -> is_read (lab (decr_ord k neq)).
Proof.
have->//: add_lab k = lab (decr_ord k neq). case: k neq=> /= m ? neq.
case: eqP=> [/neq|?]//. by apply/congr1/ord_inj.
Qed.

Arguments add_lab : simpl never.

Lemma compatible_lab_decr_ord 
  (k : 'I_N.+1) (m : nat) (r : 'I_N) (eq : r = k :> nat)
  (L : m < r) (L' : m < k) : 
  (compatible (lab     (advance r (Ordinal L)))  (lab r)) ->
  (compatible (add_lab (advance k (Ordinal L'))) (add_lab k)).
Proof.
by rewrite (add_lab_eq_nat (advance r (Ordinal L)))// (add_lab_eq_nat r).
Qed.

Equations incr_rf_codom 
  {k : 'I_N.+1} {r : 'I_N} (eq : r = k :> nat)
  (m : {l : 'I_r | (compatible (lab     (advance r l)) (lab r))}) :
       {l : 'I_k | (compatible (add_lab (advance k l)) (add_lab k))} :=
@incr_rf_codom (Ordinal L) (Ordinal L') erefl (@exist _ _ (@Ordinal m i) H) :=
  @exist _ _ (@Ordinal _ m i) (compatible_lab_decr_ord (Ordinal L) m (Ordinal L') erefl i i H).

Equations add_rf_some_aux 
  (k : 'I_N.+1) (m : 'I_N)
  (RF : compatible (lab m) (add_lab ord_max)) (IR : is_read (add_lab k)) :
  {l : 'I_k | (compatible (add_lab (advance k l)) (add_lab k))} :=
add_rf_some_aux (@Ordinal k' L) _ _ _ with Nat.eq_dec N k' := {
  add_rf_some_aux (Ordinal L) _ _ IR (right p) := 
  incr_rf_codom (decr_ord_ord (Ordinal L) p) (rff _ (decr_ord (Ordinal L) p) (is_read_add_lab (Ordinal L) p IR));
  add_rf_some_aux (Ordinal L) m RF IR (left erefl) :=
  (@exist _ (fun m => compatible (add_lab (advance (Ordinal L) m)) (add_lab (Ordinal L)))
  m (advance_is_read L RF))
}.

(*Definition add_rf_some_aux : forall
  (k : 'I_N.+1) (m : 'I_N)
  (RF : compatible (lab m) (add_lab ord_max)) (IR : is_read (add_lab k)),
  {l : 'I_k | (compatible (add_lab (advance k l)) (add_lab k))} :=
  (fun '(Ordinal k' L) =>
  match N =P k' with
  | ReflectF p => fun _ _ IR => 
      incr_rf_codom (decr_ord_ord (Ordinal L) p) (rff (decr_ord (Ordinal L) p) (is_read_add_lab (Ordinal L) p IR))
  | ReflectT eq => match eq, L with erefl, L => fun m RF IR =>
  (@exist _ (fun m => compatible (add_lab (advance (Ordinal L) m)) (add_lab (Ordinal L)))
            m (advance_is_read L RF))
  end end).*)

Definition add_rf_some : forall (m : 'I_N) (RF : compatible (lab m) l) 
  (k : 'I_N.+1) (IR : is_read (add_lab k)),
  {l : 'I_k | (compatible (add_lab (advance k l)) (add_lab k))} :=
  fun m => match (@add_lab_N (ltnSn N)) with
             erefl => fun (RF : compatible (lab m) (add_lab ord_max)) k IR =>
                        add_rf_some_aux k m RF IR
           end.

Lemma ord_P {L} : (~ is_read l) -> (~ is_read (add_lab (@Ordinal N.+1 N L))).
Proof. by rewrite add_lab_N. Qed.

Equations add_rf_None_aux  
  (k : 'I_N.+1)
  (NR : ~ is_read l)
  (IR : is_read (add_lab k)) :
  {l : 'I_k | (compatible (add_lab (advance k l)) (add_lab k))} :=
add_rf_None_aux (@Ordinal k' L) _ _ with Nat.eq_dec N k' := {
  add_rf_None_aux (Ordinal L) _ IR (right p) :=
  incr_rf_codom (decr_ord_ord (Ordinal L) p) (rff _ (decr_ord (Ordinal L) p) (is_read_add_lab (Ordinal L) p IR));
  add_rf_None_aux _ NR IR (left erefl) with (ord_P NR) IR := {}
}.

(*Definition add_rf_None_aux : forall
  (k : 'I_N.+1)
  (NR : ~ is_read l)
  (IR : is_read (add_lab k)),
  {l : 'I_k | (compatible (add_lab (advance k l)) (add_lab k))} :=
  fun '(Ordinal k' L) =>
  match N =P k' with
  | ReflectF p => fun _ IR => 
      incr_rf_codom (decr_ord_ord (Ordinal L) p) (rf (decr_ord (Ordinal L) p) (is_read_add_lab (Ordinal L) p IR))
  | ReflectT eq => match eq, L with erefl, L => fun NR IR =>
      match (ord_P NR) IR with end end
  end.*)

Definition add_rf_None := fun i j k => add_rf_None_aux j i k.

End adding_event.


Section add_event_def.
Variables (e : exec_event_struct) (pre_pred : option 'I_(n e)).

Inductive add_label := 
| add_W : tid -> var -> val -> add_label
| add_R (n : 'I_(n e)) t x a : compatible (lab e n) (R t x a) -> add_label.

Definition add_event (l : add_label) := 
  match l with
  | add_W t x a      => Pack 
                         (n e).+1 
                         (add_lab (W t x a) e)
                         (add_pred e pre_pred) 
                         (add_rf_None (W t x a) e not_false_is_true)
  | add_R k t x a RF => Pack
                         (n e).+1 
                         (add_lab (R t x a) e)
                         (add_pred e pre_pred)
                         (add_rf_some (R t x a) e k RF)
  end.

Lemma n_add_event l: n (add_event l) = (n e).+1.
Proof. Admitted.

Definition ord_f_to_onat {N M} (f : 'I_N -> option 'I_M) (n : nat) : option nat :=
  (match n < N as L return (n < N = L -> _) with
   | true  => fun pf => (opt (@nat_of_ord M)) (f (Ordinal pf))
   | false => fun=> None
   end erefl).

Definition T_f_to_nat {T N} i (f : 'I_N -> T) (n : nat) : T := 
  (match n < N as L return (n < N = L -> _) with
   | true  => fun pf => (f (Ordinal pf))
   | false => fun=> i
   end erefl).


Definition opredn (e' : exec_event_struct) := ord_f_to_onat (opred e').

Definition orffn (e' : exec_event_struct)  := ord_f_to_onat (orff e').

Definition labn (e' : exec_event_struct)  := T_f_to_nat (R 0 0 dv) (lab e').

Definition ord_restr N (f : nat -> nat) (n : 'I_N) : nat := f n.

Definition lab_of_add_lab al := 
  match al with
  | add_W t x a     => W t x a
  | add_R _ t x a _ => R t x a
  end.


Lemma olabn_add_event al k: 
  labn (add_event al) k = 
  match k =P (n e).+1 with
  | ReflectF p => labn e k
  | ReflectT _ => lab_of_add_lab al
  end.
Proof. Admitted.


Lemma opredn_add_event l k: 
  opredn (add_event l) k =
  match (n (add_event l)).-1 =P k with
  | ReflectT _ => (opt (@nat_of_ord (n e))) pre_pred
  | ReflectF _ => (opredn e) k
  end.
Proof. Admitted.


End add_event_def.



Definition eq_al {e1 e2 : exec_event_struct}
    (al1 : add_label e1) (al2 : add_label e2) : bool :=
match al1, al2 with
| add_W t x a, add_W l y b         => (t == l) && (x == y) && (a == b)
| add_R n t x a _, add_R k l y b _ => 
  (n == k :> nat) && (t == l) && (x == y) && (a == b)
| _, _                             => false
end.

Section confluence.

Definition is_iso (e e' : exec_event_struct) (f : nat -> nat) :=
  ((((n e = n e') *  
   (injective (ord_restr (n e) f))) *
   ((forall k, (ord_restr (n e) f) k < n e') * (*???*)
   ((opredn e') \o f =1 (opt f) \o (opredn e)))) *
   (((orffn e') \o f =1 (opt f) \o (orffn e)) *
   ((labn e')  \o f =1 labn e)))%type.

Definition equviv (a b : exec_event_struct) := exists f, is_iso a b f.

Notation "e ~~ e'" := (equviv e e') (at level 20).

Lemma is_iso_id e : is_iso e e id.
Proof. Admitted.

Lemma equiv_refl e: e ~~ e.
Proof. exists id. exact: is_iso_id. Qed.

Lemma opt_comp {T1 T2 T3} (f : T1 -> T2) (g : T2 -> T3) y : 
 opt (fun z => g (f z)) y = (opt g) ((opt f) y).
Proof. move: y. by case. Qed.

Lemma equiv_trans {e1} e2 {e3}: e1 ~~ e2 -> e2 ~~ e3 -> e1 ~~ e3 .
Proof. Admitted.

Lemma equiv_sym e1 e2: e1 ~~ e2 -> e2 ~~ e1.
Proof. Admitted.

Implicit Type (e : cexec_event_struct).


Definition ev_rel e e' := exists k al, add_event e k al = e'.

Notation "e '-->' e'" := (ev_rel e e') (at level 20).

Inductive ev_rel_str : cexec_event_struct -> cexec_event_struct -> Prop :=
  | Base e : ev_rel_str e e
  | Step {e1} e2 e3 (ers : ev_rel_str e1 e2) (er : e2 --> e3) : ev_rel_str e1 e3.

Notation "e '-*->' e'" := (ev_rel_str e e') (at level 20).

End confluence.

End transition_system.
