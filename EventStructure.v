From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order.
From mathcomp Require Import eqtype fingraph path.
From Equations Require Import Equations.
From event_struct Require Import utilities.

Definition var := nat.
Definition tid := nat.

Section prime_event_structure.
Context {val : eqType}.

(* TODO: move to utilities *)
Definition sproof {A : Type} {P : A -> Prop} (e : {x : A | P x}) : P (sval e) := 
  @proj2_sig A P e.

Definition is_none {A : Type} : pred (option A) := 
  fun o => if o is None then true else false.

Definition is_some {A : Type} : pred (option A) := 
  fun o => if o is Some _ then true else false.

(* labels for events in event structure *)
Inductive label :=
| R : tid -> var -> val -> label
| W : tid -> var -> val -> label.

Definition is_read  l := if l is (R _ _ _) then true else false.

Definition is_write l := if l is (W _ _ _) then true else false.

Definition compatible w r := 
  match w, r with
  | (W _ x a), (R _ y b) => (x == y) && (a == b)
  | _, _                 => false
  end.

Definition thread_id l := 
  match l with
  |  (R t _ _) | (W t _ _) => t
  end.

Definition advance {n} (m : 'I_n) (k : 'I_m) : 'I_n :=
  widen_ord (ltnW (ltn_ord m)) k.

Lemma advanceE {n} (m : 'I_n) (k : 'I_m) : 
 advance m k = k :> nat.
Proof. by case: m k => ??[]. Qed.

Structure exec_event_struct := Pack {
  n    : nat;
  lab  : 'I_n -> label;
  pred : forall (m : 'I_n), option 'I_m;
  rff  : forall m : 'I_n, is_read (lab m) ->
           {l : 'I_m | (compatible (lab (advance m l)) (lab m))};
}.

Section Cause_Conflict.

Variables (es : exec_event_struct) (l : label).

Notation n := (n es).
Notation lab := (lab es).
Notation pred := (pred es).
Notation rff := (rff es).
Notation ltn_ind := (@ltn_ind n).

(* TODO: rename *)
Definition opred e : option 'I_n :=
  if (pred e) is some e' then 
    some (advance e e') 
  else 
    None.

Definition rpred e1 e2 := opred e1 == some e2.

Definition rsucc e1 e2 := opred e2 == some e1.

Lemma pred_le e1 e2 : opred e1 = some e2 -> (e2 < e1)%N.
Proof. rewrite /opred. case: (pred e1)=> [y' [<-]|] //=. Qed.

Lemma rsucc_le e1 e2 : rsucc e1 e2 -> e1 < e2.
Proof. rewrite /rsucc. by move /eqP/pred_le. Qed.


Definition oread (e : 'I_n) : option { e : 'I_n | is_read (lab e) } := 
  insub e.

Definition owrite (e : 'I_n) : option { e : 'I_n | is_write (lab e) } := 
  insub e.

Definition orff (e : 'I_n) : option 'I_n :=
  omap 
    (fun r => 
       let rv  := sval   r in 
       let rpf := sproof r in 
       advance rv (sval (rff rv rpf))
    ) 
    (oread e).

Lemma orff_le r w : orff r = some w -> (w < r)%N.
Proof.
  rewrite /orff /oread.
  case b: (is_read (lab r)); last first.
  { rewrite insubF //=. }
  rewrite insubT //=. case=> H.
  rewrite -H advanceE. 
  apply: ltn_ord. 
Qed.

Definition rf : rel 'I_n := 
  fun w r => orff r == some w.

Lemma rf_le w r : rf w r -> w < r.
Proof. rewrite /rf. by move /eqP/orff_le. Qed.

(* Lemma orff_dom : pfun_dom orff =1 (fun e => is_read (lab e)). *)
(* Proof. admit. Admitted. *)

(* Lemma orff_read (r : 'I_n) (rH : is_read (lab r)) :  *)
(*   orff r = some (nat_of_ord (sval (rff r rH))). *)

Arguments advance : simpl never.

Definition pre_cause : rel 'I_n := 
  fun e1 e2 => rsucc e1 e2 || rf e1 e2.

Definition cause := connect [rel e1 e2 | pre_cause e1 e2].

Lemma pre_cause_lt e1 e2 : pre_cause e1 e2 -> e1 < e2.
Proof. rewrite /pre_cause. by move /orP=> [/rsucc_le | /rf_le]. Qed.

Lemma rsucc_cause x y : rsucc x y -> cause x y.
Proof. move=> H. apply/connect1. by rewrite /pre_cause /= H. Qed.

Lemma rff_cause e1 e2 : rf e1 e2 -> cause e1 e2.
Proof. move=> H. apply/connect1. by rewrite /pre_cause /= H. Qed.

Lemma refl_cause: reflexive cause.
Proof. exact: connect0. Qed.

Lemma trans_cause: transitive cause.
Proof. exact: connect_trans. Qed.

Lemma cause_decr e1 e2 : (e1 != e2) -> cause e1 e2 ->
  exists e3, cause e1 e3 && pre_cause e3 e2. 
Proof.
  move=> neq /connectP[].
  elim/last_ind=> /=.
  { move=> _ eq. move: eq neq=>-> /eqP nn. by exfalso. }
  move=> s a IHx. rewrite last_rcons rcons_path=> /swap-> /andP[*].
  exists (last e1 s). apply/andP. split=> //=. 
  apply/connectP. by exists s.
Qed.

Lemma cause_sub_leq e1 e2 : cause e1 e2 -> e1 <= e2.
Proof.
  move: e2. elim /ltn_ind=> e2 IHe2 ce12.
  case H: (e1 == e2); move: H.
  { by move=> /eqP ->. }
  move /negbT/cause_decr/(_ ce12)=> [] e3. 
  move /andP=> [ce13 /pre_cause_lt lt_e32].
  apply /ltnW /(leq_ltn_trans _ lt_e32).  
  by apply: (IHe2 e3). 
Qed.

Lemma anti_cause: antisymmetric cause.
Proof.
  move=> x y /andP[/cause_sub_leq xy /cause_sub_leq yx].
  by apply/ord_inj/anti_leq/andP.
Qed.

Definition lt_of_cause e1 e2 := (e2 != e1) && (cause e1 e2).

Lemma lt_neq_le : forall e1 e2, lt_of_cause e1 e2 = (e2 != e1) && (cause e1 e2).
Proof. done. Qed.

Definition orderMixin :=
  LePOrderMixin lt_neq_le refl_cause anti_cause trans_cause.

Definition ev_display : unit.
Proof. exact: tt. Qed.

Canonical predrderType := POrderType ev_display 'I_n orderMixin.

Import Order.LTheory.
Open Scope order_scope.
Import Order.NatOrder.

(*Notation "x <=c y" := (@Order.le ev_display _ x y) (at level 10).*)

(* base of conflict relation *)
Definition pre_conflict e1 e2 := [&& (e1 != e2), opred e1 == opred e2 & (thread_id (lab e1) == thread_id (lab e2))].

Equations conflict (e1 e2 : 'I_n) : bool by wf (e1 + e2) lt :=
  conflict e1 e2 := 
    [|| pre_conflict e1 e2,
     (match opred e1 as ox return (opred e1 = ox -> _) with
      | some x => fun=> conflict x e2
      | _      => fun=> false
      end erefl),
     (match opred e2 as oy return (opred e2 = oy -> _) with
      | some y => fun=> conflict e1 y
      | _      => fun=> false
      end erefl),
     (match orff e1 as ox return (orff e1 = ox -> _) with
      | some x => fun=> conflict x e2
      | _      => fun=> false
      end erefl) |
     (match orff e2 as oy return (orff e2 = oy -> _) with
      | some y => fun=> conflict e1 y
      | _      => fun=> false
      end erefl)].

Next Obligation. move: e=> /pred_le. ssrnatlia. Qed.
Next Obligation. move: e=> /pred_le. ssrnatlia. Qed.
Next Obligation. move: e=> /orff_le. ssrnatlia. Qed.
Next Obligation. move: e=> /orff_le. ssrnatlia. Qed.

Notation "a # b" := (conflict a b) (at level 10).

(* may be should merge this two lemmas *)
Lemma consist_conflictl {e1 e2 e3 : 'I_n}: e1 <= e2 -> e1 # e3 -> e2 # e3.
Proof.
(* proof using second defition of conflict *)
(*move=> C /conflictP [x [y/and3P[*]]]. apply/conflictP. exists x, y. apply/and3P;
split=>//. by apply/(trans_cause n1).*)
(* proof using first one *)
  elim/ltn_ind: e2=> e2 IHn2. 
  case EQ: (e1 == e2); move: EQ; first by move=>/eqP->. 
  move=> /negbT/cause_decr I /I [e4 /andP[O L C]].
  have/IHn2/(_ O C): (e4 < e2)%N.
  { by apply pre_cause_lt. }
  move: L. by apply_funelim (e2 # e3)=> n m /orP[]/eqP->->.
Qed.

Lemma consist_conflictr {e1 e2 e3}: e1 <= e2 -> e3 # e1 -> e3 # e2.
Proof.
(* proof using second defition of conflict *)
(*move=> C /conflictP [x [y/and3P[*]]]. apply/conflictP. exists x, y. apply/and3P;
split=>//. by apply/(trans_cause n1).*)
(* proof using first one *)
  elim/ltn_ind: e2=> e2 IHn2. 
  case EQ: (e1 == e2); move: EQ.
  { by move=>/eqP->. } 
  move=> /negbT/cause_decr I /I [e4 /andP[O L C]].
  have/IHn2/(_ O C): (e4 < e2)%N. 
  { by move: L=> /orP[/eqP/pred_le|/eqP/orff_le]. }
  move: L. by apply_funelim (e3 # e2)=> n m /orP[]/eqP->->.
Qed.
(* we cant use second definition here because we need this lemmas in         *)
(* conflictP below                                                           *)

Lemma conflictP e1 e2 : 
  reflect (exists e1' e2', [&& e1' <= e1, e2' <= e2 & pre_conflict e1' e2']) (e1 # e2).
Proof.
  elim/ltn_ind: e1 e2=> e1 IHe1. 
  elim/ltn_ind=> e2 IHe2. 
  apply: (iffP idP).
  { move: IHe2 IHe1. 
    apply_funelim (e1 # e2)=> {e1 e2} e1 e2 IHe1 IHe2 /or4P[?|||/orP[|]];
    [ by exists e1, e2; rewrite !le_refl 
    | case H: (opred e1) 
    | case H: (opred e2)
    | case H: (orff e1)
    | case H: (orff e2)
    ] =>//; move: (H).
  1: move/pred_le/IHe2 => R {}/R [x [y /and3P[]]]. 
  2: move/pred_le/IHe1 => R {}/R [x [y /and3P[?]]].
  3: move/orff_le/IHe2 => R {}/R [x [y /and3P[]]].
  4: move/orff_le/IHe1 => R {}/R [x [y /and3P[?]]].
  1,2: move: H=> /eqP/rsucc_cause C /trans_cause/(_ C) *. 
  3,4: move: H=> /eqP/rff_cause C /trans_cause/(_ C) *.
  1-4: exists x, y; by apply/and3P; split. }
  case=> [x [y/and3P[?? P]]]. 
  apply/(@consist_conflictl x)=>//.
  apply/(@consist_conflictr y)=>//. 
  move: P. by apply_funelim (x # y)=> ??->.
Qed.

Lemma symm_conflict: symmetric conflict.
Proof.
(* proof using second conflict definition *)
  move=> n m. apply/Bool.eq_true_iff_eq. 
  suff H: forall a b, a # b -> b # a.
  { by split=> /H. } 
  move=> a b /conflictP [x [y/and3P[??/and3P[*]]]]. 
  apply/conflictP.
  exists y, x. 
  apply/and3P; split=> //. 
  apply/and3P; split; by rewrite eq_sym.
Qed.
(* proof using first one *)
(*move=> n m. apply/Bool.eq_true_iff_eq. suff H: forall a b, a # b -> b # a;
first by split=> /H. move=> {m n}. elim/ltn_ind=> n IHn. elim/ltn_ind=> m.
move: IHn. apply_funelim (n # m)=> a b. apply_funelim (b # a)=> {n m} n m IHm IHn.
move=> /or4P[|||/orP[|]]. rewrite /pre_conflict.
- by rewrite (eq_sym n m) (eq_sym (osval (pred n)) _) (eq_sym (thread_id (lab n)) _)=>->.
- case EQ: (osval (pred m))=>//. by move: EQ=> /pred_le/IHm/(_ n) I /I->.
- case EQ: (osval (pred n))=>//. by move: EQ=> /pred_le/IHn I /I->.
- case EQ: (orff m)=>//. by move: EQ=> /orff_le/IHm/(_ n) I /I->.
case EQ: (orff n)=>//. by move: EQ=> /orff_le/IHn I /I->.*)

Definition consistency := [forall n, [forall m, (orff m == some n) ==> ~~ m # n]].

Hypothesis (consist : consistency).

Lemma rff_consist e1 e2 : (orff e2 = some e1) -> ~~ e2 # e1.
Proof. 
move/forallP: consist=> /(_ e1)/forallP/(_ e2)/implyP I ?; by apply/I/eqP.
Qed.

(* the proof is so big because we need to analyze of cases in conflict         *)
(* definition                                                                  *)
Lemma no_confl_cause n m: n <= m -> ~~ (n # m).
Proof.
(* set rc := rff_consist. *)
(* move: m n. elim/ltn_ind=> b IHn. elim/ltn_ind=> a IHm C. apply/negP=> CN. *)
(* pose c := a. pose d := b. have aEc: a = c; first by rewrite/c.  *)
(* have bEd: b = d; first by rewrite/d. have CN': c # d; first by rewrite/c/d. *)
(* move: d c aEc bEd CN' IHn IHm C CN. *)
(* apply_funelim (a # b)=> n m c d E1 E2 CN IHm IHn C. *)
(* rewrite -E1 -E2 in CN=> {E1 E2 c d a b}. move=> /or4P[|||/orP[]]. *)
(* - move=> /and3P[/cause_decr/(_ C) [x /andP[/orP[/eqP EQ nCx/eqP|/eqP/rc/negP F]]]]. *)
(* - rewrite EQ. move=> /pred_le xLn. move: EQ=> /eqP/rpred_cause/(IHn _ xLn)/negP. *)
(*   by move: (consist_conflictl nCx CN). *)
(* - move/consist_conflictl/(_ CN). by rewrite symm_conflict. *)
(* - case EQ: (opred n)=>//. move: (EQ)=> /eqP/rpred_cause/trans_cause/(_ C).  *)
(*   by move: EQ=> /pred_le/IHn C'/C'/negP. *)
(* - case EQ: (opred m)=>// nCNa. move: (EQ) (nCNa)=> /eqP/rpred_cause aCm.  *)
(*   move: (C)=> /consist_conflictl H{}/H mCNa. move: C. case NM: (n == m)=> C. *)
(* - move: NM EQ=> /eqP<-/pred_le/IHn/(_ aCm)/negP. by rewrite symm_conflict=> /(_ mCNa). *)
(* - move: NM=> /negbT/cause_decr/(_ C) [x /andP[/orP[/eqP|/eqP/rc/negP F]]]. *)
(* - rewrite EQ=> [[<-]]. by move: EQ=> /pred_le/IHm H/H/negP. *)
(* - move=> /consist_conflictl/(_ CN). by rewrite symm_conflict. *)
(* - case EQ: (orff n)=>//. move: (EQ)=> /eqP/rff_cause/trans_cause/(_ C). *)
(*   by move: EQ=> /orff_le/IHn C'/C'/negP. *)
(* - case EQ: (orff m)=>//. move: C=> /consist_conflictl H{}/H. by apply/negP/rc. *)
  admit.
Admitted.

Lemma irrefl_conflict : irreflexive conflict.
Proof. move=> n. apply/negbTE. by rewrite no_confl_cause// le_refl. Qed.

End Cause_Conflict.

Inductive cexec_event_struct := 
  Consist e of (consistency e).

Arguments Consist {_}.

Coercion ev_struct_of (e : cexec_event_struct) := let '(Consist e' _) := e in e'.

Canonical consist_subType := [subType for ev_struct_of].

Lemma consist_inj : injective (ev_struct_of). 
Proof. exact: val_inj. Qed.

End prime_event_structure.
