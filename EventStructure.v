From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order.
From mathcomp Require Import eqtype fingraph path.
(*From Equations Require Import Equations.*)
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

Arguments advance : simpl never.

Definition pre_ca : rel 'I_n := 
  fun e1 e2 => rsucc e1 e2 || rf e1 e2.

Definition ca := connect pre_ca.

Lemma pre_ca_lt e1 e2 : pre_ca e1 e2 -> e1 < e2.
Proof. rewrite /pre_ca. by move /orP=> [/rsucc_le | /rf_le]. Qed.

Lemma rsucc_ca x y : rsucc x y -> ca x y.
Proof. move=> H. apply/connect1. by rewrite /pre_ca /= H. Qed.

Lemma rff_ca e1 e2 : rf e1 e2 -> ca e1 e2.
Proof. move=> H. apply/connect1. by rewrite /pre_ca /= H. Qed.

Lemma ca_refl: reflexive ca.
Proof. exact: connect0. Qed.

Lemma ca_trans: transitive ca.
Proof. exact: connect_trans. Qed.

Lemma ca_decr e1 e2 : (e1 != e2) -> ca e1 e2 ->
  exists e3, ca e1 e3 && pre_ca e3 e2. 
Proof.
  move=> neq /connectP[].
  elim/last_ind=> /=.
  { move=> _ eq. move: eq neq=>-> /eqP nn. by exfalso. }
  move=> s a IHx. rewrite last_rcons rcons_path=> /swap-> /andP[*].
  exists (last e1 s). apply/andP. split=> //=. 
  apply/connectP. by exists s.
Qed.

Lemma ca_sub_leq e1 e2 : ca e1 e2 -> e1 <= e2.
Proof.
  move: e2. elim/ltn_ind=> e2 IHe2 ce12.
  case H: (e1 == e2); move: H.
  { by move=> /eqP ->. }
  move /negbT/ca_decr/(_ ce12)=> [] e3. 
  move /andP=> [ce13 /pre_ca_lt lt_e32].
  apply /ltnW /(leq_ltn_trans _ lt_e32).  
  by apply: (IHe2 e3). 
Qed.

Lemma ca_anti: antisymmetric ca.
Proof.
  move=> x y /andP[/ca_sub_leq xy /ca_sub_leq yx].
  by apply/ord_inj/anti_leq/andP.
Qed.

Definition lt_of_ca e1 e2 := (e2 != e1) && (ca e1 e2).

Lemma lt_neq_le : forall e1 e2, lt_of_ca e1 e2 = (e2 != e1) && (ca e1 e2).
Proof. done. Qed.

Definition orderMixin :=
  LePOrderMixin lt_neq_le ca_refl ca_anti ca_trans.

Definition ev_display : unit.
Proof. exact: tt. Qed.

Canonical predrderType := POrderType ev_display 'I_n orderMixin.

Import Order.LTheory.
Open Scope order_scope.
Import Order.NatOrder.

(* base of cf relation *)
Definition pre_cf e1 e2 :=
  [&& (e1 != e2), opred e1 == opred e2 & (thread_id (lab e1) == thread_id (lab e2))].

Definition cf e1 e2 :=
  [exists e1' : 'I_n, [exists e2' : 'I_n, [&& e1' <= e1, e2' <= e2 & pre_cf e1' e2']]].

Notation "a # b" := (cf a b) (at level 10).

Lemma cfP e1 e2 :
  reflect (exists e1' e2', [&& e1' <= e1, e2' <= e2 & pre_cf e1' e2']) (e1 # e2).
Proof.
apply (iffP existsP)=> [[x /existsP[y ?]]|[x [y ?]]]; exists x;
last (apply/existsP); by exists y.
Qed.

Notation cf' e1 e2 := [|| pre_cf e1 e2,
  (if opred e1 is some x then x # e2 else false),
  (if opred e2 is some y then e1 # y else false),
  (if orff  e1 is some x then x # e2 else false) |
  (if orff  e2 is some y then e1 # y else false)].

Lemma cf_symm: symmetric cf.
Proof.
  move=> ??. apply/(sameP idP)/(iffP idP)=> /cfP[x [y/and3P[?? /and3P[*]]]].
  all: apply/cfP; exists y, x; apply/and3P; split=>//; apply/and3P; split.
  all: by rewrite eq_sym.
Qed.

Lemma consist_cf {e1 e2 e3 e4}: e1 # e2 -> e1 <= e3 -> e2 <= e4 -> e3 # e4.
Proof.
  move=>/cfP[x [y/and3P[C C' ???]]]. apply/cfP. exists x, y.
  apply/and3P; split=>//; by rewrite ((le_trans C), (le_trans C')).
Qed.

Lemma cf'_cf e1 e2: cf' e1 e2 -> e1 # e2.
Proof.
  move/or4P=>[?|||/orP[]]; first by apply/cfP; exists e1, e2; rewrite !le_refl.
  all: opt_case=>/eqP H C; 
       by rewrite (consist_cf C)// /Order.le/=/ca connect1///pre_ca/rsucc/rf H.
Qed.

Lemma cfE e1 e2: e1 # e2 = cf' e1 e2.
Proof.
  apply/(sameP idP)/(iffP idP)=>[/cf'_cf|/cfP]//.
  case=> ?[?/and3P[/Prop_relP]]. elim=> [?/Prop_relP|].
  { by elim=> [?->//|??? /Prop_relP? H /orP[]/eqP->/H]/cf'_cf->. }
  by move=> ??? /Prop_relP ? IH /orP[]/eqP-> L /(IH L)/cf'_cf->.
Qed.

Definition consistency := [forall n, [forall m, (orff m == some n) ==> ~~ m # n]].

Hypothesis (consist : consistency).

Lemma rff_consist e1 e2 : (orff e2 = some e1) -> ~~ e2 # e1.
Proof. 
move/forallP: consist=> /(_ e1)/forallP/(_ e2)/implyP I ?; by apply/I/eqP.
Qed.

(* the proof is so big beca we need to analyze of cases in cf         *)
(* definition                                                                  *)
Lemma no_confl_ca n m: n <= m -> ~~ (n # m).
Proof.
set rc := rff_consist.
move: m n. elim/ltn_ind=> m IHn. elim/ltn_ind=> n IHm C. apply/negP=> CN.
move: (CN). rewrite cfE=> /or4P[|||/orP[]].
{ move=> /and3P[/ca_decr/(_ C) [x /andP[/swap/orP[]/eqP]]].
  { move=> EQ nCx /eqP. rewrite EQ=> /pred_le xLn. 
    move: EQ=> /eqP/rsucc_ca/(IHm _ xLn)/negP.
    by move: (consist_cf CN nCx (le_refl m)). }
  move/rc/negP/swap/(consist_cf CN)/(_ (le_refl m)). by rewrite cf_symm. }
{ case EQ: (opred n)=>//. move: (EQ)=> /eqP/rsucc_ca/ca_trans/(_ C).
  by move: EQ=> /pred_le/IHm C'/C'/negP. }
{ case EQ: (opred m)=>// nCNa. move: (EQ) (nCNa)=> /eqP/rsucc_ca aCm ?.
  move: (consist_cf nCNa C (le_refl _))=> mCNa. move: C. case NM: (n == m)=> C.
  { move: NM EQ=> /eqP<-/pred_le/IHm/(_ aCm)/negP. 
    by rewrite cf_symm=> /(_ mCNa). }
  move: NM=> /negbT/ca_decr/(_ C) [x /andP[/swap/orP[]/eqP]].
  { rewrite EQ=> [[<-]]. by move: EQ=> /pred_le/IHn H/H/negP. }
  move/rc/negP/swap/(consist_cf CN)/(_ (le_refl m)). by rewrite cf_symm. }
{ case EQ: (orff n)=>//. move: (EQ)=> /eqP/rff_ca/ca_trans/(_ C).
  by move: EQ=> /orff_le/IHm C'/C'/negP. }
{ case EQ: (orff m)=>// /consist_cf/(_ C (le_refl _)). by apply/negP/rc. }
Qed.

Lemma cf_irrelf : irreflexive cf.
Proof. move=> n. apply/negbTE. by rewrite no_confl_ca// le_refl. Qed.

End Cause_Conflict.

Inductive cexec_event_struct := 
  Consist e of (consistency e).

Arguments Consist {_}.

Coercion ev_struct_of (e : cexec_event_struct) := let '(Consist e' _) := e in e'.

Canonical consist_subType := [subType for ev_struct_of].

Lemma consist_inj : injective (ev_struct_of).
Proof. exact: val_inj. Qed.

End prime_event_structure.
Notation "x <=c y" := (@Order.le ev_display _ x y) (at level 10).
Notation "a # b" := (cf _ a b) (at level 10).