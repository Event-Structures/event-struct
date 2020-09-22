From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order.
From mathcomp Require Import eqtype fingraph path.
From event_struct Require Import utilities.

Definition var := nat.
Definition tid := nat.

Section PrimeEventStructure.

Context {val : eqType}.

(* ******************************************************************************** *)
(*     Label                                                                        *)
(* ******************************************************************************** *)

Inductive label :=
| R : tid -> var -> val -> label
| W : tid -> var -> val -> label.

Definition is_read  l := if l is (R _ _ _) then true else false.

Definition is_write l := if l is (W _ _ _) then true else false.

(*Definition compatible w r := 
  match w, r with
  | (W _ x a), (R _ y b) => (x == y) && (a == b)
  | _, _                 => false
  end.*)

Definition ocompatible (w r : option label) := 
  match w, r with
  | some (W _ x a), some (R _ y b) => (x == y) && (a == b)
  | _, _                 => false
  end.

Definition thread_id l := 
  match l with
  |  (R t _ _) | (W t _ _) => t
  end.

(* ******************************************************************************** *)
(*     Exec Event Structure                                                         *)
(* ******************************************************************************** *)

Structure exec_event_struct := Pack {
  n     : nat;
  lab   : 'I_n -> label;
  fpred : forall (m : 'I_n), option 'I_m;
  frf   : forall m : 'I_n, is_read (lab m) ->
            {l : 'I_m | (ocompatible (ext lab l) (ext lab m))};
}.

Section ExecEventStructure.

Variables (es : exec_event_struct) (l : label).

Notation n       := (n es).
Notation lab     := (lab es).
Notation fpred   := (fpred es).
Notation frf     := (frf es).
Notation ltn_ind := (@ltn_ind n).

(* ******************************************************************************** *)
(*     Event Types                                                                  *)
(* ******************************************************************************** *)

Definition oread (e : 'I_n) : option { e : 'I_n | is_read (lab e) } := 
  insub e.

Definition owrite (e : 'I_n) : option { e : 'I_n | is_write (lab e) } := 
  insub e.


(* ******************************************************************************** *)
(*     Predecessor and Successor                                                    *)
(* ******************************************************************************** *)

Definition ofpred e : option 'I_n :=
  omap (advance e) (fpred e).

Definition pred e1 e2 := ofpred e1 == some e2.

Definition succ e1 e2 := ofpred e2 == some e1.

Lemma ofpred_lt e1 e2 : ofpred e1 = some e2 -> e2 < e1.
Proof. rewrite /ofpred. case: (fpred e1)=> [? [<-]|] //=. Qed.

Lemma pred_lt e1 e2 : pred e1 e2 -> e2 < e1.
Proof. rewrite /pred. by move /eqP /ofpred_lt. Qed.

Lemma succ_lt e1 e2 : succ e1 e2 -> e1 < e2.
Proof. rewrite /succ. by move /eqP /ofpred_lt. Qed.

(* ******************************************************************************** *)
(*     Reads-From                                                                   *)
(* ******************************************************************************** *)

Definition ofrf (e : 'I_n) : option 'I_n :=
  omap 
    (fun r => 
       let rv  := sval   r in 
       let rpf := sproof r in 
       advance rv (sval (frf rv rpf))
    ) 
    (oread e).

Lemma ofrf_le r w : ofrf r = some w -> w < r.
Proof.
  rewrite /ofrf /oread.
  case b: (is_read (lab r)); first last.
  { by rewrite insubF. }
  rewrite insubT//= => [[<-]]/=.
  exact: ltn_ord. 
Qed.

(* Reads-From relation *)
Definition rf : rel 'I_n := 
  fun w r => ofrf r == some w.

Lemma rf_lt w r : rf w r -> w < r.
Proof. rewrite /rf. by move /eqP /ofrf_le. Qed.

(* ******************************************************************************** *)
(*     Causality                                                                    *)
(* ******************************************************************************** *)

(* Immediate causality relation *)
Definition ica : rel 'I_n := 
  fun e1 e2 => succ e1 e2 || rf e1 e2.

Lemma ica_lt e1 e2 : ica e1 e2 -> e1 < e2.
Proof. rewrite /ica. by move /orP=> [/succ_lt | /rf_lt]. Qed.


(* Causality relation *)
Definition ca := connect ica.

Lemma succ_ca x y : succ x y -> ca x y.
Proof. move=> H. apply/connect1. by rewrite /ica /= H. Qed.

Lemma rf_ca e1 e2 : rf e1 e2 -> ca e1 e2.
Proof. move=> H. apply/connect1. by rewrite /ica /= H. Qed.

Lemma ca_refl: reflexive ca.
Proof. exact: connect0. Qed.

Lemma ca_trans: transitive ca.
Proof. exact: connect_trans. Qed.

Lemma ca_decr e1 e2 : e1 != e2 -> ca e1 e2 ->
  exists e3, ca e1 e3 && ica e3 e2. 
Proof.
  move /swap/crtn1_connectP=> [/eqP // | e3 e4 ?].
  move=> /crtn1_connectP E *.
  exists e3. by rewrite /ca E. 
Qed.

Lemma ca_le e1 e2 : ca e1 e2 -> e1 <= e2.
Proof. move /crtn1_connectP. elim=> [] //. move=> ??/ica_lt. slia. Qed.

Lemma ca_anti: antisymmetric ca.
Proof.
  move=> ?? /andP[/ca_le ? /ca_le ?]. 
  apply/ord_inj; slia.
Qed.

(* Strict (irreflexive) causality *)
Definition sca e1 e2 := (e2 != e1) && (ca e1 e2).

Lemma sca_def : forall e1 e2, sca e1 e2 = (e2 != e1) && (ca e1 e2).
Proof. done. Qed.

Definition orderMixin :=
  LePOrderMixin sca_def ca_refl ca_anti ca_trans.

Definition ev_display : unit.
Proof. exact: tt. Qed.

Canonical predrderType := POrderType ev_display 'I_n orderMixin.

Import Order.LTheory.
Open Scope order_scope.
Import Order.NatOrder.

(* ******************************************************************************** *)
(*     Conflict                                                                     *)
(* ******************************************************************************** *)

(* Immediate conflict relation *)
Definition icf e1 e2 :=
  [&& (e1 != e2), ofpred e1 == ofpred e2 & (thread_id (lab e1) == thread_id (lab e2))].

Lemma icf_symm e1 e2: icf e1 e2 -> icf e2 e1.
Proof. move/and3P=>[*]. apply/and3P; split; by rewrite eq_sym. Qed.


(* Conflict relation *)
Definition cf e1 e2 :=
  [exists e1' : 'I_n, [exists e2' : 'I_n, [&& e1' <= e1, e2' <= e2 & icf e1' e2']]].

Notation "a # b" := (cf a b) (at level 10).

Lemma cfP e1 e2 :
  reflect (exists e1' e2', [&& e1' <= e1, e2' <= e2 & icf e1' e2']) (e1 # e2).
Proof. apply: existsPP => n. apply: existsPP => m. apply: idP. Qed.

Lemma cf_symm: symmetric cf.
Proof.
  move=> *. apply /(sameP idP) /(iffP idP) => /cfP[x [y /and3P[*]]].
  all: apply/cfP; exists y, x.
  all: by apply/and3P; split=> //; apply/icf_symm.
Qed.

Lemma consist_cf {e1 e2 e3 e4}: e1 # e2 -> e1 <= e3 -> e2 <= e4 -> e3 # e4.
Proof.
  move=> /cfP[x [y/and3P[C C' ???]]].
  apply/cfP; exists x, y.
  apply/and3P; split=>//; by rewrite ((le_trans C), (le_trans C')).
Qed.


Notation cf_step e1 e2 := [|| icf e1 e2,
  (if ofpred e1 is some x then x # e2 else false),
  (if ofpred e2 is some y then e1 # y else false),
  (if ofrf  e1 is some x then x # e2 else false) |
  (if ofrf  e2 is some y then e1 # y else false)].

Lemma cf_step_cf e1 e2: cf_step e1 e2 -> e1 # e2.
Proof.
  move/or4P => [? |||/orP[]].
  { apply/cfP; exists e1, e2. by rewrite !le_refl. }
  all: ocase=> /eqP H C.
  all: rewrite (consist_cf C) // /Order.le /= /ca connect1 //.
  all: by rewrite /ica /succ /rf H.
Qed.

Lemma cfE e1 e2: e1 # e2 = cf_step e1 e2.
Proof.
  apply /(sameP idP)/(iffP idP)=> [/cf_step_cf | /cfP] //.
  case=> ? [? /and3P[/crtn1_connectP]].
  elim=> [/crtn1_connectP |].
  { elim=> [-> |] //.
    by move=> ?? /orP[] /eqP-> /crtn1_connectP ? H /H /cf_step_cf->. }
  by move=> ?? /orP[] /eqP-> /crtn1_connectP ? IH L /(IH L) /cf_step_cf->.
Qed.

(* ******************************************************************************** *)
(*     Reads-From Consistency                                                       *)
(* ******************************************************************************** *)

Definition consistency := [forall n, [forall m, (ofrf m == some n) ==> ~~ m # n]].

Hypothesis (consist : consistency).

Lemma rff_consist {e1 e2} : (ofrf e2 = some e1) -> ~ e2 # e1.
Proof. 
  move/forallP: consist=> /(_ e1)/forallP/(_ e2)/implyP I ?.
  by apply/negP/I/eqP.
Qed.

Lemma cf_irrelf : irreflexive cf.
Proof.
  move=> m. apply/negbTE/negP.
  elim/ltn_ind: m=> m IHn.
  suff C: forall n, ofpred m = some n -> ~ m # n.
  { rewrite cfE=> /or4P[|||/orP[]]; ocase.
    { by rewrite/icf eq_refl. }
    1,2: move/C; by rewrite // cf_symm.
    1,2: move/rff_consist; by rewrite // cf_symm. }
  move=> k /swap /cfP[x [y /and3P[]]]. case E: (x == m).
  { move/eqP :E =>-> ? /ca_le ? /and3P[? /eqP-> ? /eqP /succ_lt].
    slia. }
  move/negbT/ca_decr: E => /apply.
  case=> z /andP[? /orP[] /eqP E1 L ? E2].
  { apply/(IHn z).
    { by apply /succ_lt /eqP. }
    apply/cfP; exists x, y.
    apply/and3P; split=>//.
    by move: E1 E2=>->[->]. }
  apply/(rff_consist E1)/cfP.
  exists y, x; apply/and3P; split=>//.
  { by apply /(le_trans L) /succ_ca /eqP. }
  by rewrite icf_symm.
Qed.

End ExecEventStructure.

Inductive cexec_event_struct := Consist e of (consistency e).

Arguments Consist {_}.

Coercion ev_struct_of (e : cexec_event_struct) := let '(Consist e' _) := e in e'.

Canonical consist_subType := [subType for ev_struct_of].

Lemma consist_inj : injective (ev_struct_of).
Proof. exact: val_inj. Qed.

End PrimeEventStructure.

Notation "x <=c y" := (@Order.le ev_display _ x y) (at level 10).
Notation "a # b" := (cf _ a b) (at level 10).
