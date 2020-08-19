From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order eqtype div fingraph path. 
From Equations Require Import Equations.
From event_struct Require Import ssrlia.
Definition var := nat.
Definition thread_id := nat.

Notation sw := 
   (ltac:(let f := fresh "_top_" in let s := fresh "_s_" in move=> f s; move: s f)).

Lemma snd_true3 a b : [|| a, true | b].
Proof. by case: a. Qed.

Lemma trd_true3 a b : [|| b, a | true].
Proof. by case: a; case b. Qed.

Lemma snd_true2 a : a || true.
Proof. by case: a. Qed.

Lemma frth_true4 a b c: [|| a, b, c | true].
Proof. by case: a; case: b; case: c. Qed.

Lemma fifth_true5 a b c d: [|| a, b, c, d | true].
Proof. apply/orP; right. exact: frth_true4. Qed.

Lemma ltnnn {n}: ~ (n < n).
Proof. ssrnatlia. Qed.

Lemma ltS_neq_lt {n N}: n < N.+1 -> N <> n -> n < N.
Proof. ssrnatlia. Qed. 

Hint Resolve trd_true3 snd_true3 snd_true2 frth_true4 fifth_true5 : core.

Definition osval {T} {P : T -> bool} (ok : {? k : T | P k }) : option T := 
  if ok is some k then some (sval k) else None.

Lemma ltn_ind N (P : 'I_N -> Type) :
  (forall (n : 'I_N), (forall (m : 'I_N), m < n -> P m) -> P n) ->
  forall n, P n.
Proof.
move=> IH n. have [k le_size] := ubnP (nat_of_ord n). 
elim: k n le_size=>// n IHn k le_size. apply/IH=> *. apply/IHn. ssrnatlia.
Qed.

Section prime_event_structure.
Context {val : eqType}.

(* labels for events in event structure *)
Inductive label :=
| R : thread_id -> var -> val -> label
| W : thread_id -> var -> val -> label.

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
  po : forall (m : 'I_n), {? k : 'I_n | k < m};
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

(* Section with definitions for execution graph with added event *)
Section adding_event.
Variable 
  (lab : label)               (* label of an event which we want to add      *)
  (e : execgraph)             (* execution graph in which we want to add lab *)
  (pre_po : option 'I_(n e)). (* po-child of new event (if it exists)        *)
Notation N := (n e).
Notation E := (E e).
Notation po := (po e).
Notation rf := (rf e).

(*Equations add_E (n : 'I_N.+1) : label :=
add_E (@Ordinal n L) with equal N n := {
  add_E _ (left erefl) := lab;
  add_E (Ordinal L) (right p) := E (Ordinal (ltS_neq_lt L p))
}.*)

Definition add_E : 'I_N.+1 -> label := fun '(@Ordinal _ n L) =>
  if equal N n is right p then E (Ordinal (ltS_neq_lt L p)) else lab.

(*Equations incr_ord (m : 'I_N) : 'I_N.+1 :=
incr_ord (@Ordinal n L) := @Ordinal _ n (ltn_trans L (ltnSn _)).*)

(* incrementing of ordinal number *)
Definition incr_ord : 'I_N -> 'I_N.+1 := 
  fun '(@Ordinal _ n L) => @Ordinal _ n (ltn_trans L (ltnSn _)).

(* add_E correctness *)
Lemma add_E_incr_ord m : E m = add_E (incr_ord m).
Proof.
case: m=> /= m L. case: (equal N m)=> [EQ|?]; last by apply/congr1/ord_inj.
move: EQ L. case: m / => L. exfalso. ssrnatlia.
(* proof for Equations version *)
(*funelim (incr_ord m). funelim (add_E (Ordinal (ltn_trans i (ltnSn N)))). 
- exfalso. case: eqargs=> E. move: E i0=>->. ssrnatlia.
case: eqargs=> EQ. by apply/congr1/ord_inj.*)
Qed.

(* auxiliary lemma  *)
Lemma incr_is_read {m} {L} L' : read_from (E m)                (add_E (@Ordinal _ N L)) ->
                                read_from (add_E (incr_ord m)) (add_E (@Ordinal _ N L')).
Proof.
rewrite add_E_incr_ord. have->//: (add_E (Ordinal L)) = (add_E (Ordinal L')).
by apply/congr1/ord_inj.
Qed.

(*Equations incr_oord (n : option 'I_N) : option 'I_N.+1 :=
incr_oord (some (Ordinal L)) := some (Ordinal (ltn_trans L (ltnSn N)));
incr_oord None := None.*)

(* 'option' version for 'inc_ord' *)
Definition incr_oord (n : option 'I_N) : option 'I_N.+1 := 
  if n is some n then some (incr_ord n) else None.

Lemma nltn0 n: ~ (n < 0).
Proof. ssrnatlia. Qed.

(*Equations incr_po_codom {m : 'I_N} (k : {? k : 'I_N | k < m}) : {? k : 'I_N.+1 | k < m} :=
incr_po_codom (some (@exist _ _ (Ordinal L) L')) :=
  some (@exist _ _ (Ordinal (ltn_trans L (ltnSn _))) L');
incr_po_codom None := None.*)

(* here we define function that incrementing ordinal in po-codomain type to *)
(* use it in add_po function in (1)                                         *)
Definition incr_po_codom {m : 'I_N} (k : {? k : 'I_N | k < m}) : {? k : 'I_N.+1 | k < m} := 
  if k is some (@exist _ _ (Ordinal _ L) L') 
    then some (@exist _ _ (Ordinal (ltn_trans L (ltnSn _))) L')
  else None.

(*Equations add_po (pre_n : option 'I_N) (n : 'I_N.+1) : {? k : 'I_N.+1 | k < n} :=
add_po on (@Ordinal _ n L) with equal N n := {
  add_po None _ (left erefl) := None;
  add_po (some (Ordinal L')) (Ordinal L) (left erefl) :=
    some (@exist _ _ (Ordinal (ltn_trans L' (ltnSn _))) L');
  add_po _ (Ordinal L) (right p) := incr_po_codom (po (Ordinal (ltS_neq_lt L p)))
}.*)
(* may we should to use definition with Equalites here *)
Definition add_po (l : 'I_N.+1) : {? k : 'I_N.+1 | k < l} :=
  match l with (Ordinal n L) => 
    match equal N n with
    | left eq =>  
      match eq with erefl => 
        if pre_po is some  (Ordinal _ L') 
          then some (@exist _ _ (Ordinal (ltn_trans L' (ltnSn _))) L')
        else None 
      end
    | right p  => incr_po_codom (po (Ordinal (ltS_neq_lt L p)))     (* (1) *)
    end
  end.

Lemma and_i {a b : bool} : a -> b -> a && b.
Proof. by move=>->. Qed.

(*Equations decr_ord (l : 'I_N.+1) (neq : N <> l) : 'I_N :=
decr_ord (Ordinal L) neq := Ordinal (ltS_neq_lt L neq).*)

(* if l \in 'I_N.+1 and l <> N then we can convert it's type to 'I_N *)
Definition decr_ord : forall (l : 'I_N.+1) (neq : N <> l), 'I_N :=
  fun '(Ordinal n L) neq => Ordinal (ltS_neq_lt L neq).

(* auxiliary lemma *)
Lemma is_read_add_E_E l neq: is_read (add_E l) -> is_read (E (decr_ord l neq)).
Proof.
have->//: add_E l = E (decr_ord l neq). case: l neq=> /= m ? neq.
case: (equal N m)=> [/neq|?]//. by apply/congr1/ord_inj.
(*have->//: add_E l = E (decr_ord l neq). funelim (add_E l); first by case: neq.
simp decr_ord. by apply/congr1/ord_inj.*)
Qed.

(*Equations decr_rf_dom (k : {l : 'I_N.+1 | is_read (add_E l)}) 
                        (neq : N <> (sval k)) : 
                        {l : 'I_N | is_read (E l)} :=
decr_rf_dom (@exist (Ordinal L) IR) neq :=
  @exist _ _ (Ordinal (ltS_neq_lt L neq)) (is_read_add_E_E _ neq IR).*)

(* to use rf in add_rf_some definition in (2) we have to make it suitable    *)
(* with rf (convert type of add_rf-domain to rf's-domain)                    *)
Definition decr_rf_dom : forall (k : {l : 'I_N.+1 | is_read (add_E l)})
                                (neq : N <> (sval k)),
                                {l : 'I_N | is_read (E l)} := 
  fun '(@exist _ _ (Ordinal n L) IR) neq => 
    @exist _ _ (Ordinal (ltS_neq_lt L neq)) (is_read_add_E_E _ neq IR).


Lemma and_e1 {a b}: a && b -> a.
Proof. by case: a. Qed.

Lemma and_e2 {a b}: a && b -> b.
Proof. by case: a. Qed.

Lemma nat_of_incr_od (l : 'I_N) : (incr_ord l) = l :> nat.
Proof. (*by funelim (incr_ord l)*) by case: l. Qed.

Lemma incr_ord_le {l r : 'I_N}: l < r -> incr_ord l < incr_ord r.
Proof. by rewrite !nat_of_incr_od. Qed.

(* auxiliary lemma *)
Lemma read_from_incr_ord {l r : 'I_N}: read_from (E l) (E r) ->
  read_from (add_E (incr_ord l)) (add_E (incr_ord r)).
Proof. by rewrite !add_E_incr_ord. Qed.

(*Equations incr_rf_codom 
  (k : {l : 'I_N.+1 | is_read (add_E l)})
  (r : {l : 'I_N | is_read (E l)}) (eq : incr_ord (sval r) = sval k)
  (m : {l : 'I_N    | (l < (sval r)) && (read_from (E l)     (E     (sval r)))}) :
       {l : 'I_N.+1 | (l <  sval k) &&  (read_from (add_E l) (add_E (sval k)))} :=
incr_rf_codom (@exist _ _) _ erefl (@exist l COND) :=
  @exist _ _ (incr_ord l) (and_i (incr_ord_le (and_e1 COND)) (read_from_incr_ord (and_e2 COND))).*)

(* when we have result of rf in (3) we have to convert it's type to add_rf's *)
(* codomain type, so we convert do this with 'm'                             *)
Definition incr_rf_codom : forall
  (k : {l : 'I_N.+1 | is_read (add_E l)})  
  (r : {l : 'I_N    | is_read (E l)}) (eq : incr_ord (sval r) = sval k) (* <- (4) *)
  (m : {l : 'I_N    | (l < (sval r)) && (read_from (E l)     (E     (sval r)))}),
       {l : 'I_N.+1 | (l <  sval k) &&  (read_from (add_E l) (add_E (sval k)))} := 
  fun _ _ 'erefl '(@exist _ _ l COND) =>
  @exist _ _ (incr_ord l) (and_i (incr_ord_le (and_e1 COND)) (read_from_incr_ord (and_e2 COND))).

(* we are going to use it for proof of eq in (4) *)
Lemma sval_decr_ord (k : {l : 'I_N.+1 | is_read (add_E l)}) :
  forall p, incr_ord (sval (decr_rf_dom k p)) = sval k.
Proof.
case: k=> [[*]]/=. by apply/ord_inj.
Qed.

(* adding read-event to rf *)
Equations add_rf_some
  (m : 'I_N) (RF : read_from (E m) (add_E ord_max))
  (k : {l : 'I_N.+1 | is_read (add_E l)}) :
       {l : 'I_N.+1 | (l < sval k) && (read_from (add_E l) (add_E (sval k)))} :=
add_rf_some _ _ k with equal N (sval k) := {
  add_rf_some (Ordinal m_le_N) RF (@exist (Ordinal L) _) (left erefl) :=
    (@exist _ _ (incr_ord (Ordinal m_le_N)) (and_i m_le_N (incr_is_read L RF)));
  add_rf_some _ _ k (right p) :=  incr_rf_codom k _ (sval_decr_ord _ _) (rf (decr_rf_dom k p))
                                           (* (3) *)                        (* (2) *)
}.
(* this definitions fail's... *)
(*??? Definition add_rf_some : forall
  (m : 'I_N) (RF : read_from (E m) (add_E ord_max))
  (k : {l : 'I_N.+1 | is_read (add_E l)}),
       {l : 'I_N.+1 | (l < sval k) && (read_from (add_E l) (add_E (sval k)))} := 
  fun '(Ordinal _ m_le_N) RF k => 
  match k with (@exist _ _ (Ordinal l L) _) =>
    match equal N l with
    | left eq => match eq, L with erefl, L' => 
                  (@exist _ _ (incr_ord (Ordinal m_le_N)) (and_i m_le_N (incr_is_read L' RF)))
                 end
    | right p => incr_rf_codom k _ (sval_decr_ord _ _) (rf (decr_rf_dom k p)) 
    end
  end.*)


Lemma ord_P {L} : (~ is_read (add_E ord_max)) -> (~ is_read (add_E (@Ordinal N.+1 N L))).
Proof. have->//: ord_max = (@Ordinal N.+1 N L). by apply/ord_inj. Qed.

(* adding write event to rf *)
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
Notation ltn_ind := (ltn_ind N).

Definition rpo x y := osval (po x) == some y.

Definition orf (n : 'I_N) : option 'I_N :=
  (if is_read (E n) as r return (is_read (E n) = r -> _)
    then fun pf => some (sval (rf (@exist _ _ n pf)))
  else fun=> None) erefl.

Lemma orf_le n m: orf n = some m -> m < n.
Proof.
rewrite/orf.
case: {2}(is_read (E n)) {-1}(@erefl _ (is_read (E n))) erefl=> {2 3}->// ?[].
by case: (rf _)=>/= x /andP[?? <-].
Qed.

Lemma po_le n m: osval (po n) = some m -> m < n.
Proof. by case: (po n)=> //= [[/=??[<-]]]. Qed.

Definition rrf (n m : 'I_N) : bool := (orf n == some m).

Definition cause := connect [rel m n | rrf n m || rpo n m].

Lemma rpo_cause n m: rpo n m -> cause m n.
Proof. move=> H. apply/connect1. by rewrite/= H. Qed.

Lemma rrf_cause n m: rrf n m -> cause m n.
Proof. move=> H. apply/connect1. by rewrite/= H. Qed.

Lemma refl_cause: reflexive cause.
Proof. exact: connect0. Qed.

Lemma trans_cause: transitive cause.
Proof. exact: connect_trans. Qed.

Lemma cause_decr n m: (n != m) -> cause n m ->
  exists k, (((rpo m k) || (orf m == some k)) && cause n k).
Proof.
move=> nm /connectP[].
elim/last_ind=> /=.
- move=> _ eq. move: eq nm=>-> /eqP nn. by exfalso.
move=> x a IHx. rewrite last_rcons rcons_path=> /sw-> /andP[*].
exists (last n x). apply/andP. split=> //=; first by rewrite orbC.
apply/connectP. by exists x.
Qed.

Lemma cause_sub_leq n m : cause n m -> n <= m.
Proof.
move: m. elim/ltn_ind => m IHm cmn.
case H: (n == m); move: H.
- by move=> /eqP ->.
move/negbT/cause_decr/(_ cmn)=> [] k /andP[/orP[/eqP /po_le|/eqP /orf_le]] km cnk;
apply/ltnW/(@leq_ltn_trans k n m)=> //; exact: (IHm k km cnk).
Qed.

Lemma anti_cause: antisymmetric cause.
Proof.
move=> x y /andP[/cause_sub_leq xy /cause_sub_leq yx].
by apply/ord_inj/anti_leq/andP.
Qed.

(* base of conflict relation *)
Definition pre_conflict n m := [&& (n != m), osval (po n) == osval (po m) & (tid (E n) == tid (E m))].

Equations conflict (n m : 'I_N) : bool by wf (n + m) lt :=
conflict n m := [|| pre_conflict n m,
(match osval (po n) as ox return (osval (po n) = ox -> _) with
| some x => fun=> conflict x m
| _      => fun=> false
end erefl),
(match osval (po m) as ox return (osval (po m) = ox -> _) with
| some x => fun=> conflict n x
| _      => fun=> false
end erefl),
(match orf n as ox return (orf n = ox -> _) with
| some x => fun=> conflict x m
| _      => fun=> false
end erefl) |
(match orf m as ox return (orf m = ox -> _) with
| some x => fun=> conflict n x
| _      => fun=> false
end erefl)].

Next Obligation. move: e0=> /po_le. ssrnatlia. Qed.
Next Obligation. move: e0=> /po_le. ssrnatlia. Qed.
Next Obligation. move: e0=> /orf_le. ssrnatlia. Qed.
Next Obligation. move: e0=> /orf_le. ssrnatlia. Qed.

Notation "a # b" := (conflict a b) (at level 10).

(* may be should merge this two lemmas *)
Lemma consist_conflictl {n1 n2 n3}: cause n1 n2 -> n1 # n3 -> n2 # n3.
Proof.
(* proof using second defition of conflict *)
(*move=> C /conflictP [x [y/and3P[*]]]. apply/conflictP. exists x, y. apply/and3P;
split=>//. by apply/(trans_cause n1).*)
(* proof using first one *)
elim/ltn_ind: n2=> n2 IHn2. case EQ: (n1 == n2); move: EQ;
first by move=>/eqP->. move=> /negbT/cause_decr I /I [k /andP[O L C]].
have/IHn2/(_ L C): k < n2; first by move: O=> /orP[/eqP/po_le|/eqP/orf_le].
move: O. by apply_funelim (n2 # n3)=> n m /orP[]/eqP->->.
Qed.

Lemma consist_conflictr {n1 n2 n3}: cause n1 n2 -> n3 # n1 -> n3 # n2.
Proof.
(* proof using second defition of conflict *)
(*move=> C /conflictP [x [y/and3P[*]]]. apply/conflictP. exists x, y. apply/and3P;
split=>//. by apply/(trans_cause n1).*)
(* proof using first one *)
elim/ltn_ind: n2=> n2 IHn2. case EQ: (n1 == n2); move: EQ;
first by move=>/eqP->. move=> /negbT/cause_decr I /I [k /andP[O L C]].
have/IHn2/(_ L C): k < n2; first by move: O=> /orP[/eqP/po_le|/eqP/orf_le].
move: O. by apply_funelim (n3 # n2)=> n m /orP[]/eqP->->.
Qed.
(* we cant use second definition here because we need this lemmas in         *)
(* conflictP below                                                           *)

Lemma conflictP n m : 
  reflect (exists x y, [&& cause x n, cause y m & pre_conflict x y]) (n # m).
Proof.
elim/ltn_ind: n m=> n IHn. elim/ltn_ind=> m IHm. apply: (iffP idP).
- move: IHm IHn. apply_funelim (n # m)=> {n m} n m IHm IHn /or4P[?|||/orP[|]];
  [by exists n, m; rewrite !refl_cause | case H : (osval (po n))|
  case H : (osval (po m))|case H : (orf n)|case H : (orf m)]=>//; move: (H).
  move/po_le/IHn => R {}/R [x [y /and3P[]]].
  2: move/po_le/IHm => R {}/R [x [y /and3P[?]]].
  3: move/orf_le/IHn => R {}/R [x [y /and3P[]]].
  4: move/orf_le/IHm => R {}/R [x [y /and3P[?]]].
  1,2: move: H=> /eqP/rpo_cause C /trans_cause/(_ C) *. 
  3,4: move: H=> /eqP/rrf_cause C /trans_cause/(_ C) *.
  1-4: exists x, y; by apply/and3P; split.
case=> [x [y/and3P[?? P]]]. apply/(@consist_conflictl x)=>//.
apply/(@consist_conflictr y)=>//. move: P. by apply_funelim (x # y)=> ??->.
Qed.

Lemma symm_conflict: symmetric conflict.
Proof.
(* proof using second conflict definition *)
move=> n m. apply/Bool.eq_true_iff_eq. suff H: forall a b, a # b -> b # a;
first by split=> /H. move=> a b /conflictP [x [y/and3P[??/and3P[*]]]]. apply/conflictP.
exists y, x. apply/and3P; split=> //. apply/and3P; split; by rewrite eq_sym.
(* proof using first one *)
(*move=> n m. apply/Bool.eq_true_iff_eq. suff H: forall a b, a # b -> b # a;
first by split=> /H. move=> {m n}. elim/ltn_ind=> n IHn. elim/ltn_ind=> m.
move: IHn. apply_funelim (n # m)=> a b. apply_funelim (b # a)=> {n m} n m IHm IHn.
move=> /or4P[|||/orP[|]]. rewrite /pre_conflict.
- by rewrite (eq_sym n m) (eq_sym (osval (po n)) _) (eq_sym (tid (E n)) _)=>->.
- case EQ: (osval (po m))=>//. by move: EQ=> /po_le/IHm/(_ n) I /I->.
- case EQ: (osval (po n))=>//. by move: EQ=> /po_le/IHn I /I->.
- case EQ: (orf m)=>//. by move: EQ=> /orf_le/IHm/(_ n) I /I->.
case EQ: (orf n)=>//. by move: EQ=> /orf_le/IHn I /I->.*)
Qed.

Definition rf_consist := forall n m, (orf m = some n) -> ~~ m # n.

Hypothesis (rc : rf_consist).

(* the proof is so big because we need to analyze of cases in conflict         *)
(* definition                                                                  *)
Lemma no_confl_cause n m: cause n m -> ~~ (n # m).
Proof.
move: m n. elim/ltn_ind=> b IHn. elim/ltn_ind=> a IHm C. apply/negP=> CN.
pose c := a. pose d := b. have aEc: a = c; first by rewrite/c. 
have bEd: b = d; first by rewrite/d. have CN': c # d; first by rewrite/c/d.
move: d c aEc bEd CN' IHn IHm C CN.
apply_funelim (a # b)=> n m c d E1 E2 CN IHm IHn C.
rewrite -E1 -E2 in CN=> {E1 E2 c d a b}. move=> /or4P[|||/orP[]].
- move=> /and3P[/cause_decr/(_ C) [x /andP[/orP[/eqP EQ nCx/eqP|/eqP/rc/negP F]]]].
- rewrite EQ. move=> /po_le xLn. move: EQ=> /eqP/rpo_cause/(IHn _ xLn)/negP.
  by move: (consist_conflictl nCx CN).
- move/consist_conflictl/(_ CN). by rewrite symm_conflict.
- case EQ: (osval (po n))=>//. move: (EQ)=> /eqP/rpo_cause/trans_cause/(_ C). 
  by move: EQ=> /po_le/IHn C'/C'/negP.
- case EQ: (osval (po m))=>// nCNa. move: (EQ) (nCNa)=> /eqP/rpo_cause aCm. 
  move: (C)=> /consist_conflictl H{}/H mCNa. move: C. case NM: (n == m)=> C.
- move: NM EQ=> /eqP<-/po_le/IHn/(_ aCm)/negP. by rewrite symm_conflict=> /(_ mCNa).
- move: NM=> /negbT/cause_decr/(_ C) [x /andP[/orP[/eqP|/eqP/rc/negP F]]].
- rewrite EQ=> [[<-]]. by move: EQ=> /po_le/IHm H/H/negP.
- move=> /consist_conflictl/(_ CN). by rewrite symm_conflict.
- case EQ: (orf n)=>//. move: (EQ)=> /eqP/rrf_cause/trans_cause/(_ C).
  by move: EQ=> /orf_le/IHn C'/C'/negP.
- case EQ: (orf m)=>//. move: C=> /consist_conflictl H{}/H. by apply/negP/rc.
Qed.

Lemma irrefl_conflict : irreflexive conflict.
Proof. move=> n. apply/negbTE. by rewrite no_confl_cause// refl_cause. Qed.


End Cause_Conflict.

End prime_event_structure.
