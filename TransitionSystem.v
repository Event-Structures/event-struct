From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order.
From mathcomp Require Import eqtype fingraph path. 
From event_struct Require Import utilities EventStructure.
From Coq Require Import Arith.
From Equations Require Import Equations.
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

(* add_lab correctness second lemma *)
Lemma add_lab_N {L : N < N.+1}: add_lab (Ordinal L) = l.
Proof. move=> /=. by case: eqP. Qed.


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
  incr_rf_codom (decr_ord_ord (Ordinal L) p) (frf (decr_ord (Ordinal L) p) (is_read_add_lab (Ordinal L) p IR));
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
  incr_rf_codom (decr_ord_ord (Ordinal L) p) (frf (decr_ord (Ordinal L) p) (is_read_add_lab (Ordinal L) p IR));
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
Variables (e : exec_event_struct) (ipred : option 'I_(n e)).

Inductive add_label := 
| add_W : tid -> var -> val -> add_label
| add_R (n : 'I_(n e)) t x a : compatible (lab e n) (R t x a) -> add_label.

Definition add_event (l : add_label) := 
  match l with
  | add_W t x a      => Pack 
                         (n e).+1 
                         (add_lab (W t x a) e)
                         (add_pred e ipred) 
                         (add_rf_None (W t x a) e not_false_is_true)
  | add_R k t x a RF => Pack
                         (n e).+1 
                         (add_lab (R t x a) e)
                         (add_pred e ipred)
                         (add_rf_some (R t x a) e k RF)
  end.

Definition opredn (e' : exec_event_struct) := 
  ord_dom_to_nat (ofpred e') (omap (@nat_of_ord _)).

Definition ofrfn (e' : exec_event_struct)  := 
  ord_dom_to_nat (ofrf e') (omap (@nat_of_ord _)).

Definition olabn (e' : exec_event_struct)  := 
  ord_dom_to_nat (lab e') some.

Definition lab_of_add_lab al := 
  match al with
  | add_W t x a     => W t x a
  | add_R _ t x a _ => R t x a
  end.

Definition write_of_add_lab al := 
  match al with
  | add_W _ _ _     => None
  | add_R n _ _ _ _ => some n
  end.

Lemma olabn_add_event al k: 
  olabn (add_event al) k = 
  match n e =P k with (* TODO Replace with 'n e' *)
  | ReflectF p => olabn e k
  | ReflectT _ => some (lab_of_add_lab al)
  end.
Proof.
rewrite/olabn/ord_dom_to_nat.
set tn := n e.
case: {2}(k < n (add_event al)) {-1}(@erefl _ (k < n (add_event al))) erefl=> {2 3}->;
case: {2}(k < n e) {-1}(@erefl _ (k < n e)) erefl=> {2 3}->;
case: al; case: eqP=> //=.
- move=> eq t v s kne kne1. by case: eqP.
- move=> neq t v s kne kne1. case: eqP=> //= nek.
  have: kne = ltS_neq_lt kne1 nek. exact: eq_irrelevance. by move=>->.
- move=> eq n t v s comp kne kne1. by case: eqP.
- move=> neq n t v s comp kne kne1. case: eqP=> //= nek.
  have: kne = ltS_neq_lt kne1 nek. exact: eq_irrelevance. by move=>->.
- move=> eq t v s knef kne1. by case: eqP.
- move=> neq t v s knef kne1. case: eqP=> //= *.
  have: n e = k=> //. apply/eqP. by rewrite eqn_leq leqNgt knef -ltnS kne1.
- move=> eq n t v s comp knef kne1. by case: eqP.
- move=> neq n t v s comp knef kne1. case: eqP=> //.
  have: tn = k=> //. apply/eqP. by rewrite eqn_leq leqNgt knef -ltnS kne1.
- move=> eq t v s ktn kne1f.
  have: k < k. apply: (ltn_trans ktn). by rewrite ltnNge -ltnS kne1f.
  by rewrite ltnn.
- move=> neq _ _ _ ktn kne1f. have: k < k. 
  apply: (ltn_trans ktn). by rewrite ltnNge -ltnS kne1f.
  by rewrite ltnn.
- move=> eq n t v s comp ktn ktn1f. have: k < k.
  apply: (ltn_trans ktn). by rewrite ltnNge -ltnS ktn1f.
  by rewrite ltnn.
- move=> neq n t v s comp ktn kne1f. have: k < k.
  apply: (ltn_trans ktn). by rewrite ltnNge -ltnS kne1f.
  by rewrite ltnn.
- move=> eq t v s ktnf. by rewrite -eq leqNgt ltnn.
move=> eq n t v s comp ktnf. by rewrite -eq leqNgt ltnn.
Qed.

Lemma opredn_add_event l k: 
  opredn (add_event l) k = 
  match n e =P k with 
  | ReflectT _ => (omap (@nat_of_ord (n e))) ipred
  | ReflectF _ => (opredn e) k
  end.
Proof. Admitted.

Lemma opredn_le k l: 
  opredn e k = some l -> l < n e.
Proof.
rewrite/opredn/ord_dom_to_nat. dep_case=>// ?. 
by case E: (ofpred e _)=> [[]/=|//][<-].
Qed.

Lemma ofrfn_le k l: 
  ofrfn e k = some l -> l < n e.
Proof.
rewrite/ofrfn/ord_dom_to_nat. dep_case=>// L. 
by case E: (ofrf e (Ordinal L)) => [[]/=|//][<-].
Qed.

Lemma n_add_event l: n (add_event l) = (n e).+1.
Proof. by case: l. Qed.

Lemma n_add_event_le_n al: n e <= n (add_event al).
Proof. by rewrite n_add_event. Qed.

Lemma orff_add_event al y :
  ofrf (add_event al) y = 
  (match y < n e as Lxn return (y < n e = Lxn -> _) with
  | true  => fun pf => if (ofrf e (Ordinal pf)) is Some a
                           then some (widen_ord (@n_add_event_le_n _) a)
                       else None
  | false => fun=> if (write_of_add_lab al) is Some a
                     then some (widen_ord (@n_add_event_le_n _) a)
                   else None
  end) erefl.
Proof. Admitted.

Lemma ofrfn_add_event l k: 
  ofrfn (add_event l) k =
  match n e =P k with
  | ReflectT _ => (omap (@nat_of_ord (n e))) (write_of_add_lab l)
  | ReflectF _ => (ofrfn e) k
  end.
Proof.
case: eqP; rewrite/ofrfn/ord_dom_to_nat.
- dep_case=> [L?|]; last (rewrite n_add_event; slia).
  rewrite orff_add_event/=. dep_case; first (by move=>*; exfalso; slia).
  by case: l L.
do ?dep_case=>//.
- move=> L *. rewrite orff_add_event/=. dep_case; last by rewrite L.
  move=> L'. have->: (Ordinal L') = (Ordinal L) by apply/ord_inj.
  by case: (ofrf e (Ordinal (n:=n e) (m:=k) L)).
all: move=> ? L ?; exfalso; rewrite n_add_event in L; slia.
Qed.

End add_event_def.

Implicit Type (e : exec_event_struct).

Definition ev_rel e e' := exists k al, add_event e k al = e'.

Notation "e '-->' e'" := (ev_rel e e') (at level 20).

Inductive ev_rel_str : exec_event_struct -> exec_event_struct -> Prop :=
  | Base e : ev_rel_str e e
  | Step {e1} e2 e3 (ers : ev_rel_str e1 e2) (er : e2 --> e3) : ev_rel_str e1 e3.

Notation "e '-*->' e'" := (ev_rel_str e e') (at level 20).

Definition add_place e e' k := exists al, add_event e k al = e'.

Lemma ev_rel_ord_le {e1 e }: e1 -*-> e -> n e1 <= n e.
Proof. elim=> // ?????[?[l <-]]. rewrite/add_event. case: l=>/= *; slia. Qed.

Arguments add_lab : simpl never.

End transition_system.

Notation "e '-->' e'" := (ev_rel e e') (at level 20).

Notation "e '-*->' e'" := (ev_rel_str e e') (at level 20).