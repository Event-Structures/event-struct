From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order.
From mathcomp Require Import eqtype fingraph path. 
From event_struct Require Import utilities EventStructure.

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

Context {val : eqType}.
Notation exec_event_struct := (@exec_event_struct val).
Implicit Types (e : exec_event_struct) (x : var) (a : val) (t : tid).
Notation label := (@label val).
Notation n := (@n val).




(* Section with definitions for execution graph with added event *)
Section adding_event.
Variable 
  (lab : label)               (* label of an event which we want to add      *)
  (e : exec_event_struct)     (* execution graph in which we want to add lab *)
  (pre_po : option 'I_(n e)). (* po-child of new event (if it exists)        *)
Notation N := (n e).
Notation Lab := (Lab e).
Notation po := (po e).
Notation rf := (rf e).


Definition add_Lab : 'I_N.+1 -> label := fun '(@Ordinal _ n L) =>
  if N =P n is ReflectF p then Lab (Ordinal (ltS_neq_lt L p)) else lab.

(* add_Lab correctness first lemma *)
Lemma add_Lab_incr_ord m {K: N < N.+1} : Lab m = add_Lab (incr (Ordinal K) m).
Proof.
case: m=> /= m L. case: eqP=> [EQ|?]; last by apply/congr1/ord_inj.
move: EQ L. case: m / => L. exfalso. ssrnatlia.
Qed.

(* add_Lab correctness second lemma *)
Lemma add_Lab_N {L : N < N.+1}: add_Lab (Ordinal L) = lab.
Proof. move=> /=. by case: eqP. Qed.


Definition add_po (m : 'I_N.+1) : option 'I_m := 
  let '(Ordinal m' L) := m in 
  match N =P m' with
  | ReflectT eq => let 'erefl := eq in pre_po
  | ReflectF p => (po (Ordinal (ltS_neq_lt L p))) 
  end.

(* if l \in 'I_N.+1 and l <> N then we can convert it's type to 'I_N *)
Definition decr_ord : forall (l : 'I_N.+1) (neq : N <> l), 'I_N :=
  fun '(Ordinal n L) neq => Ordinal (ltS_neq_lt L neq).

Lemma decr_ord_ord k p: (decr_ord k p) = k :> nat.
Proof. by case: k p. Qed.

(* auxiliary lemma  *)
Lemma incr_is_read {K: N < N.+1} {m : 'I_(Ordinal K)} {L} L' : 
  compatible (Lab m)                        (add_Lab (@Ordinal _ N L)) ->
  compatible (add_Lab (incr (Ordinal K) m)) (add_Lab (@Ordinal _ N L')).
Proof.
rewrite add_Lab_incr_ord. have->//: (add_Lab (Ordinal L)) = (add_Lab (Ordinal L')).
by apply/congr1/ord_inj.
Qed.

(* auxiliary lemma *)
Lemma is_read_add_Lab l neq: 
  is_read (add_Lab l) -> is_read (Lab (decr_ord l neq)).
Proof.
have->//: add_Lab l = Lab (decr_ord l neq). case: l neq=> /= m ? neq.
case: eqP=> [/neq|?]//. by apply/congr1/ord_inj.
Qed.

Arguments add_Lab : simpl never.

Lemma compatible_Lab_decr_ord 
  (k : 'I_N.+1) (l : nat) (r : 'I_N) (eq : r = k :> nat)
  (L : l < r) (L' : l < k) : 
  (compatible (Lab     (incr r (Ordinal L)))  (Lab r)) ->
  (compatible (add_Lab (incr k (Ordinal L'))) (add_Lab k)).
Proof.
case: r k eq L L'=> ? L [? L' /= E L1 L2/=]. 
have<-: Lab (Ordinal L) = add_Lab (Ordinal L').
- rewrite /add_Lab. case: eqP=> E'; first by exfalso; ssrnatlia.
- by apply/congr1/ord_inj.
- have<-//: (Lab (incr (Ordinal L) (Ordinal L1))) =
        (add_Lab (incr (Ordinal L') (Ordinal L2)))=>/=.
- rewrite /add_Lab; case: eqP=> E'; first by exfalso; ssrnatlia.
by apply/congr1/ord_inj.
Qed.

Equations incr_rf_codom 
  {k : 'I_N.+1} {r : 'I_N} (eq : r = k :> nat)
  (l : {l : 'I_r | (compatible (Lab     (incr r l)) (Lab r))}) :
       {l : 'I_k | (compatible (add_Lab (incr k l)) (add_Lab k))} :=
@incr_rf_codom (Ordinal L) (Ordinal L') erefl (@exist _ _ (@Ordinal m i) H) :=
  @exist _ _ (@Ordinal _ m i) (compatible_Lab_decr_ord (Ordinal L) m (Ordinal L') erefl i i H).

Definition add_rf_some_aux : forall
  (k : 'I_N.+1) (m : 'I_N)
  (RF : compatible (Lab m) (add_Lab ord_max)) (IR : is_read (add_Lab k)),
  {l : 'I_k | (compatible (add_Lab (incr k l)) (add_Lab k))} :=
  (fun '(Ordinal k' L) =>
  match N =P k' with
  | ReflectF p => fun _ _ IR => 
      incr_rf_codom (decr_ord_ord (Ordinal L) p) (rf (decr_ord (Ordinal L) p) (is_read_add_Lab (Ordinal L) p IR))
  | ReflectT eq => match eq, L with erefl, L => fun m RF IR =>
  (@exist _ (fun m => compatible (add_Lab (incr (Ordinal L) m)) (add_Lab (Ordinal L))) m (incr_is_read L RF))
  end end).

Definition add_rf_some : forall (m : 'I_N) (RF : compatible (Lab m) lab) 
  (k : 'I_N.+1) (IR : is_read (add_Lab k)),
  {l : 'I_k | (compatible (add_Lab (incr k l)) (add_Lab k))} :=
  fun m => match (@add_Lab_N (ltnSn N)) with
             erefl => fun (RF : compatible (Lab m) (add_Lab ord_max)) k IR =>
                        add_rf_some_aux k m RF IR
           end.

Lemma ord_P {L} : (~ is_read lab) -> (~ is_read (add_Lab (@Ordinal N.+1 N L))).
Proof. by rewrite add_Lab_N. Qed.

Definition add_rf_None_aux : forall
  (k : 'I_N.+1)
  (NR : ~ is_read lab)
  (IR : is_read (add_Lab k)),
  {l : 'I_k | (compatible (add_Lab (incr k l)) (add_Lab k))} :=
  fun '(Ordinal k' L) =>
  match N =P k' with
  | ReflectF p => fun _ IR => 
      incr_rf_codom (decr_ord_ord (Ordinal L) p) (rf (decr_ord (Ordinal L) p) (is_read_add_Lab (Ordinal L) p IR))
  | ReflectT eq => match eq, L with erefl, L => fun NR IR =>
      match (ord_P NR) IR with end end
  end.

Definition add_rf_None := fun i j k => add_rf_None_aux j i k.

End adding_event.


(* derive cause conflict and properties ... *)

Section add_event_def.
Variables (e : exec_event_struct) (pre_po : option 'I_(n e)).

Inductive add_label := 
| add_W : tid -> var -> val -> add_label
| add_R (n : 'I_(n e)) t x a : compatible (Lab e n) (R t x a) -> add_label.

Definition add_event (l : add_label) := 
  match l with
  | add_W t x a      => Pack 
                         (n e).+1 
                         (add_Lab (W t x a) e)
                         (add_po e pre_po) 
                         (add_rf_None (W t x a) e (is_read_W t x a))
  | add_R k t x a RF => Pack
                         (n e).+1 
                         (add_Lab (R t x a) e)
                         (add_po e pre_po)
                         (add_rf_some (R t x a) e k RF)
  end.
End add_event_def.

Definition equviv e e' :=
  ((n e' = n e) * 
  (exists (f : 'I_(n e) -> 'I_(n e')), 
  ((injective f) * (*???*)
  ((opo e') \o f =1 (opt f) \o (opo e))) *
  (((orf e') \o f =1 (opt f) \o (orf e)) *
  ((Lab e')   \o f =1 Lab e))))%type.

Notation "e ~~ e'" := (equviv e e') (at level 0).

Lemma equiv_refl e: e ~~ e.
Proof.
split=>//. exists id; split; split=>//; move=>?/=; rewrite/opt; 
first by case: (opo _ _). by  by case: (orf _ _).
Qed.

Lemma equiv_trans e1 e2 e3: e1 ~~ e2 -> e2 ~~ e3 -> e1 ~~ e3 .
Proof. Admitted.

Definition ev_rel (e e' : exec_event_struct) := exists al k, add_event e k al = e'.

Notation "e '-->' e'" := (ev_rel e e') (at level 20).

Inductive ev_rel_str : exec_event_struct -> exec_event_struct -> Prop :=
  | Base e : ev_rel_str e e
  | Steap e1 e2 e3 (ers : ev_rel_str e1 e2) (er : e2 --> e3) : ev_rel_str e1 e3.

Notation "e '-*->' e'" := (ev_rel_str e e') (at level 20).

Print ex.
Print ordinal_ind.
(*Definition add_place e e' : e --> e' -> (option 'I_(n e)) := 
  fun '(@ex_intro _ _ _ (@ex_intro _ _ k _)) => k.*)

Definition confluence_rel e1 e2 :=
  exists e3 e3', (((e1 -*-> e3) * (e2 -*-> e3')) * (e3 ~~ e3'))%type.

Notation "e ~c~ e'" := (confluence_rel e e') (at level 0).

(*Lemma confluence_symm e1 e2: e1 ~c~ e2 -> e2 ~c~ e1.
Proof. Admitted.*)

Lemma confuense_add e1 e2 e1' : 
  e1 ~c~ e2 -> e1 --> e1' -> e1' ~c~ e2.
Proof. Admitted.
(*case=> e [e'[[*]]].*)

Hint Resolve equiv_refl Base : core.

Theorem confluence e e1 e2 : e -*-> e1 -> e -*-> e2 -> 
  e1 ~c~ e2.
Proof. elim=> [*|? l ?? H ?/H?]; by [exists e2, e2|apply/(confuense_add l)]. Qed.

End transition_system.
