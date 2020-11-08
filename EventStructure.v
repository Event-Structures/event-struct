From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order choice.
From mathcomp Require Import eqtype fingraph path.
From event_struct Require Import utilities relations InhType.

Definition var := nat.

Inductive label {Rval Wval : Type} :=
| Read of var & Rval
| Write of var & Wval
| ThreadStart
| ThreadEnd.

Canonical inhlabel (Rval Wval : Type) := 
  Inhabitant (@label Rval Wval) ThreadEnd.

Section PrimeEventStructure.

Context {val : eqType}.

(* ******************************************************************************** *)
(*     Label                                                                        *)
(* ******************************************************************************** *)

Local Notation label := (@label val val).

Implicit Type (l : label).

Definition is_read  l := if l is (Read _ _) then true else false.

Definition is_thdstart l := if l is ThreadStart then true else false.

Definition compatible (w r : label) := 
  match w, r with
  | (Write x a), (Read y b) => (x == y) && (a == b)
  | _, _                 => false
  end.

Notation is_read_ext f r := (is_read (ext f r)).

Notation compatible_ext f := (compatible \o2 (ext f)).

(* ******************************************************************************** *)
(*     Exec Event Structure                                                         *)
(* ******************************************************************************** *)

Structure exec_event_struct := Pack {
  n     : nat;
  lab   : 'I_n -> label;
  fpred : forall m : 'I_n, option 'I_m;
  frf   : forall (r : 'I_n) (is_r : is_read_ext lab r), 
            {w : 'I_r | compatible_ext lab w r} 
}.

Section ExecEventStructure.

Variables (es : exec_event_struct).

Notation n       := (n es).
Notation lab     := (lab es).
Notation fpred   := (fpred es).
Notation frf     := (frf es).

(* ******************************************************************************** *)
(*     Event Types                                                                  *)
(* ******************************************************************************** *)

Definition oread (e : nat) : {? e : 'I_n | is_read (ext lab e) } := 
  oapp insub none (insub_ord n e).

(* ******************************************************************************** *)
(*     Predecessor and Successor                                                    *)
(* ******************************************************************************** *)

Definition ofpred (e : nat) : option nat :=
  obind (fun (a : 'I_n) => omap (@nat_of_ord a) (fpred a)) (insub_ord n e).

Lemma ofpred_n m (_ : m >= n) : ofpred m = none.
Proof. rewrite /ofpred. insub_case. slia. Qed.


Definition pred e1 e2 := ofpred e1 == some e2.

Definition succ e1 e2 := ofpred e2 == some e1.

Lemma ofpred_lt e1 e2 : ofpred e1 = some e2 -> e2 < e1.
Proof.
  rewrite /ofpred. insub_case=> L. by case: (fpred _)=> //= [[/= ?? [<-]]].
Qed.

Lemma pred_lt e1 e2 : pred e1 e2 -> e2 < e1.
Proof. rewrite /pred. by move /eqP /ofpred_lt. Qed.

Lemma succ_lt e1 e2 : succ e1 e2 -> e1 < e2.
Proof. rewrite /succ. by move /eqP /ofpred_lt. Qed.

(* ******************************************************************************** *)
(*     Reads-From                                                                   *)
(* ******************************************************************************** *)

Definition ofrf (e : nat) : option nat := 
  omap (fun r => (nat_of_ord (sval (frf _ (svalP r))))) (oread e).

Lemma ofrf_n m (_ : m >= n) : ofrf m = none.
Proof. rewrite /ofrf /oread. insub_case. slia. Qed.

Lemma ofrf_le r w : ofrf r = some w -> w < r.
Proof.
  rewrite /ofrf /oread. insub_case=> L. case H: (is_read_ext lab (ord L)).
  { rewrite insubT /= => [[<-]]. by case: (sval (frf (ord L) H)). }
  by rewrite insubF.
Qed.

(* Reads-From relation *)
Definition rf : rel nat := 
  fun w r => ofrf r == some w.

Lemma rf_lt w r : rf w r -> w < r.
Proof. rewrite /rf. by move /eqP /ofrf_le. Qed.

(* ******************************************************************************** *)
(*     Causality                                                                    *)
(* ******************************************************************************** *)

(* Immediate causality relation *)
Definition ica : rel nat := 
  fun e1 e2 => succ e1 e2 || rf e1 e2.

Lemma ica_lt e1 e2 : ica e1 e2 -> e1 < e2.
Proof. rewrite /ica. by move /orP=> [/succ_lt | /rf_lt]. Qed.

(* Causality relation *)
Definition ca := rt_cl ica.

Lemma succ_ca x y : succ x y -> ca x y.
Proof. move=> ?. apply /irel_rt_cl. by apply /orP; left. Qed.

Lemma rf_ca e1 e2 : rf e1 e2 -> ca e1 e2.
Proof. move=> ?. apply /irel_rt_cl. by apply /orP; right. Qed.

Lemma ca_refl: reflexive ca.
Proof. exact: rt_cl_refl. Qed.

Lemma ca_trans: transitive ca.
Proof. exact: rt_cl_trans. Qed.

Arguments ca_trans {_ _ _}.

Lemma ca_decr e1 e2 : e1 != e2 -> ca e1 e2 ->
  exists e3, ca e1 e3 && ica e3 e2. 
Proof.
  move /swap/closureP=> [/eqP // | e3 e4 ?].
  move=> /closureP E *.
  exists e3. by rewrite /ca E. 
Qed.

Lemma ca_le e1 e2 : ca e1 e2 -> e1 <= e2.
Proof. move /closureP. elim=> [] //. move=> ??/ica_lt. slia. Qed.

Lemma ca_rfield e1 e2 (_ : ca e1 e2) : (e1 == e2) || (e1 < n) && (e2 < n).
Proof.
  case N: (e1 == e2)=> //=. apply/andP. suff E: (e2 < n).
  { split=> //. move /ca_le: H. slia. }
  move /closureP: H N. elim=> [/eqP|? e] //.
  rewrite /ica /succ /rf. case H: (e < n)=> //. have ?: (e >= n) by slia.
  by rewrite ofrf_n ?ofpred_n.
Qed.

Lemma ca_anti: antisymmetric ca.
Proof. move=> ?? /andP[/ca_le ? /ca_le ?]. slia. Qed.

(* Strict (irreflexive) causality *)
Definition sca e1 e2 := (e2 != e1) && (ca e1 e2).

Lemma sca_def : forall e1 e2, sca e1 e2 = (e2 != e1) && (ca e1 e2).
Proof. done. Qed.

Definition orderMixin :=
  LePOrderMixin sca_def ca_refl ca_anti (@ca_trans).

Definition ev_display : unit.
Proof. exact: tt. Qed.

(* TODO: make this canonocal projection work *)
Canonical predorderType := POrderType ev_display nat orderMixin.

Import Order.LTheory.
Open Scope order_scope.
Import Order.NatOrder.

(* ******************************************************************************** *)
(*     Conflict                                                                     *)
(* ******************************************************************************** *)


(* Immediate conflict relation *)
Definition icf (e1 e2 : nat) :=
  [&& (e1 != e2),
      ofpred e1 == ofpred e2,
      ~~ is_thdstart (ext lab e1) &
      ~~ is_thdstart (ext lab e2)].

Lemma icf_symm e1 e2: icf e1 e2 -> icf e2 e1.
Proof. move/and3P=>[??/andP[*]]. apply/and4P; split; by rewrite 1?eq_sym. Qed.

(* Conflict relation *)
Definition cf e1 e2 :=
  [exists e1' : 'I_e1.+1, [exists e2' : 'I_e2.+1,
  [&& ca e1' e1, ca e2' e2 & icf e1' e2']]].

Notation "a # b" := (cf a b) (at level 10).

Lemma cfP {e1 e2}:
  reflect (exists e1' e2', [&& ca e1' e1, ca e2' e2 & icf e1' e2']) (e1 # e2).
Proof.
  apply (iffP existsP).
  { case=> [[m ? /existsP[[/= n ?]]]]. by exists m, n. }
  case=> x [y /and4P[Lc1 Lc2 *]]. move /ca_le: (Lc1) (Lc2) => L1 /ca_le L2.
  exists (@Ordinal e1.+1 _ L1). apply /existsP. exists (@Ordinal e2.+1 _ L2).
  by apply /and4P.
Qed.

Lemma cf_symm: symmetric cf.
Proof.
  move=> *. apply /(sameP idP) /(iffP idP) => /cfP[x [y /and3P[*]]].
  all: apply/cfP; exists y, x.
  all: by apply/and3P; split=> //; apply/icf_symm.
Qed.

Lemma consist_cf {e1 e2 e3 e4}: e1 # e2 -> ca e1 e3 -> ca e2 e4 -> e3 # e4.
Proof.
  move=> /cfP[x [y/and3P[C C' ???]]].
  apply/cfP; exists x, y.
  apply/and3P; split=>//; by rewrite ((ca_trans C), (ca_trans C')).
Qed.

Notation cf_step e1 e2 := [|| icf e1 e2,
  (if ofpred e1 is some x then x # e2 else false),
  (if ofpred e2 is some y then e1 # y else false),
  (if ofrf  e1 is some x then x # e2 else false) |
  (if ofrf  e2 is some y then e1 # y else false)].

Lemma cf_step_cf e1 e2: cf_step e1 e2 -> e1 # e2.
Proof.
  move/or4P => [? |||/orP[]].
  { apply/cfP; exists e1, e2. by rewrite !ca_refl. }
  all: ocase=> /eqP H C.
  all: rewrite (consist_cf C) // ?ca_refl // /ca irel_rt_cl //.
  all: by rewrite /ica /succ /rf H.
Qed.

Lemma cfE e1 e2: e1 # e2 = cf_step e1 e2.
Proof.
  apply /(sameP idP)/(iffP idP)=> [/cf_step_cf | /cfP] //.
  case=> ? [? /and3P[/closureP]].
  elim=> [/closureP |].
  { elim=> [-> |] //.
    by move=> ?? /orP[] /eqP-> /closureP ? H /H /cf_step_cf->. }
  by move=> ?? /orP[] /eqP->/closureP ? IH L /(IH L) /cf_step_cf->.
Qed.

(* ******************************************************************************** *)
(*     Reads-From Consistency                                                       *)
(* ******************************************************************************** *)

Definition consistency := [forall k : 'I_n, [forall m : 'I_n,
   (ofrf m == some (nat_of_ord k)) ==> ~~ m # k]].

Hypothesis consist : consistency.

Lemma rff_consist {e1 e2} (rf : ofrf e2 = some e1) : ~ e2 # e1.
Proof.
  suff L: (e2 < n)%N.
  { move /ofrf_le: (rf)=> L1. have L3: (e1 < n)%N by slia.
    move /forallP /(_ (Ordinal L3)) /forallP /(_ (Ordinal L)): consist.
    by move /eqP : rf=> /swap /implyP /apply /negP. }
  move: rf. rewrite /ofrf /oread. by insub_case. 
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
  { move/eqP :E =>-> ? /ca_le ? /and3P[? /eqP-> ? /eqP /succ_lt]. slia. }
  move/negbT/ca_decr: E => /apply.
  case=> z /andP[? /orP[] /eqP E1 L ? E2].
  { apply/(IHn z).
    { exact /succ_lt /eqP. }
    apply/cfP; exists x, y.
    apply/and3P; split=>//.
    by move: E1 E2=>->[->]. }
  apply/(rff_consist E1)/cfP.
  exists y, x; apply/and3P; split=>//.
  { exact /(ca_trans L) /succ_ca /eqP. }
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
Notation te_ext := (ext ThreadEnd).
Notation is_read_ext f r := (is_read (ext f r)).
Notation compatible_ext f := (compatible \o2 (ext f)).
