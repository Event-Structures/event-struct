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
  | _, _                    => false
  end.

Notation is_read_ext f r := (is_read (ext f r)).

Notation compatible_ext f := (relpre (ext f) compatible).

(* ******************************************************************************** *)
(*     Exec Event Structure                                                         *)
(* ******************************************************************************** *)

Structure exec_event_struct := Pack {
  N     : nat;
  lab   : 'I_N -> label;
  fpred : forall m : 'I_N, 'I_m.+1;
  frf   : forall (r : 'I_N), {w : 'I_r.+1 |
                             (~~ compatible_ext lab w r) ==> (w == r :> nat)}
}.

Section ExecEventStructure.

Variables (es : exec_event_struct).

Notation N       := (N es).
Notation lab     := (lab es).
Notation fpred   := (fpred es).
Notation frf     := (frf es).

(* ******************************************************************************** *)
(*     Event Types                                                                  *)
(* ******************************************************************************** *)

Definition oread (e : nat) : {? e : 'I_N | is_read (ext lab e) } := 
  obind insub (insub e).

(* ******************************************************************************** *)
(*     Predecessor and Successor                                                    *)
(* ******************************************************************************** *)

Definition fpredn (e : nat) : nat := if insub e is some k then fpred k else e.

Definition pred e1 e2 := (e1 != e2) && (fpredn e1 == e2).

Definition succ e1 e2 := (e1 != e2) && (fpredn e2 == e1).

Lemma fpredn_lt e: fpredn e <= e.
Proof. rewrite /fpredn. insub_case=> ?? <-. by case: (fpred _). Qed.

Lemma pred_lt e1 e2 : pred e1 e2 -> e2 < e1.
Proof. case/andP. move: (fpredn_lt e1). slia. Qed.

Lemma succ_lt e1 e2 : succ e1 e2 -> e1 < e2.
Proof. case/andP. move: (fpredn_lt e2). slia. Qed.

(* ******************************************************************************** *)
(*     Reads-From                                                                   *)
(* ******************************************************************************** *)

Definition frfn (e : nat) : nat := 
  if insub e is some k then sval (frf k) else e.

Lemma frfn_lt r : frfn r <= r.
Proof. rewrite /frfn. insub_case=> ?? <-. case: (sval (frf _)). slia. Qed.

(* Reads-From relation *)
Definition rf w r := (w != r) && (frfn r == w).

Lemma rf_lt w r : rf w r -> w < r.
Proof. case/andP. move: (frfn_lt r). slia. Qed.

(* ******************************************************************************** *)
(*     Causality                                                                    *)
(* ******************************************************************************** *)

(* Immediate causality relation *)
Definition ica : rel nat := 
  fun e1 e2 => succ e1 e2 || rf e1 e2.

Lemma ica_lt e1 e2 : ica e1 e2 -> e1 < e2.
Proof. by move /orP=> [/succ_lt | /rf_lt]. Qed.

Lemma ica_lt_N e1 e2: ica e1 e2 -> e2 < N.
Proof. case/orP=>/andP[]; rewrite /fpredn /frfn; insub_case; slia. Qed.

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

Lemma ca_rfield e1 e2 : ca e1 e2 -> (e1 == e2) || (e1 < N) && (e2 < N).
Proof.
  case NE: (e1 == e2)=> //= C. apply/andP. suff E: (e2 < N).
  { split=> //. move /ca_le: C. slia. }
  move /closureP: C NE. by elim=> [/eqP|??] // /ica_lt_N.
Qed.

Lemma ca_anti: antisymmetric ca.
Proof. move=> ?? /andP[/ca_le ? /ca_le ?]. slia. Qed.

Lemma ca_fpredn {e}: ca (fpredn e) e.
Proof.
  case E: (fpredn e != e); last (move/eqP: E->; by rewrite ca_refl).
  apply/irel_rt_cl. rewrite /ica. by rewrite /succ eq_refl E.
Qed.

Lemma ca_frfn e : ca (frfn e) e.
Proof.
  case E: (frfn e != e); last (move/eqP: E->; by rewrite ca_refl).
  apply/irel_rt_cl. rewrite /ica. by rewrite /rf eq_refl E.
Qed.


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
      fpredn e1 == fpredn e2,
      (fpredn e1 < e1)%N,
      (fpredn e2 < e2)%N,
      ~~ is_thdstart (ext lab e1) &
      ~~ is_thdstart (ext lab e2)].


Lemma icf_symm e1 e2: icf e1 e2 -> icf e2 e1.
Proof. case/and5P=>*. apply/and5P; split; try slia. by rewrite andbC. Qed.

(* Conflict relation *)
Definition cf e1 e2 :=
  [exists e1' : 'I_e1.+1, [exists e2' : 'I_e2.+1,
  [&& ca e1' e1, ca e2' e2 & icf e1' e2']]].

Notation "a # b" := (cf a b) (at level 10).

Lemma cfP {e1 e2}:
  reflect (exists e1' e2', [&& ca e1' e1, ca e2' e2 & icf e1' e2']) (e1 # e2).
Proof.
  apply (iffP existsP).
  { case=> [[m ? /existsP[[/= N ?]]]]. by exists m, N. }
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

Notation cf_step e1 e2 := 
  [|| icf e1 e2,
  (fpredn e1) # e2,  e1 # (fpredn e2),
  (frfn   e1) # e2 | e1 # (frfn   e2)].

Lemma cf_step_cf e1 e2: cf_step e1 e2 -> e1 # e2.
Proof.
  move/or4P => [|||/orP[]]=> H.
  { apply/cfP; exists e1, e2. by rewrite !ca_refl. }
  all: apply/(consist_cf H)=> //; by rewrite ?ca_refl ?ca_fpredn ?ca_frfn.
Qed.

Lemma cfE e1 e2: e1 # e2 = cf_step e1 e2.
Proof.
  apply /(sameP idP)/(iffP idP)=> [/cf_step_cf | /cfP] //.
  case=> ? [? /and3P[/closureP]].
  elim=> [/closureP |].
  { elim=> [-> |] //.
    by move=> ?? /orP[]/andP[?] /eqP-> /closureP ? H /H /cf_step_cf->. }
  by move=> ?? /orP[]/andP[?] /eqP->/closureP ? IH L /(IH L) /cf_step_cf->.
Qed.

(* ******************************************************************************** *)
(*     Reads-From Consistency                                                       *)
(* ******************************************************************************** *)

Definition consistency := [forall e : 'I_N, ~~ e # (frfn e)].

Hypothesis consist : consistency.

Lemma rff_consist e : ~ e # (frfn e).
Proof.
  move=> c. suff L: (e < N)%N. 
  { by move /forallP /(_ (ord L)) /negP: consist c. }
  case L: (e < N)=> //. move: c. rewrite /frfn.
  insub_case=> ? /cfP[?[? /and3P[/ca_rfield/orP[/eqP->|/andP[]//]]]].
  by case/ca_rfield/orP=> [/eqP->|/andP[//]] /andP[/eqP].
Qed.

Lemma cf_irrelf : irreflexive cf.
Proof.
  move=> m. apply/negbTE/negP.
  elim/ltn_ind: m=> m IHn.
  suff C: ~ m # (fpredn m).
  { rewrite cfE=> /or4P[|||/orP[]] //.
    1-3: rewrite /icf (eq_refl, cf_symm) //.
    all: exact/rff_consist. }
  move=> /cfP[x [y /and3P[]]]. case E: (x == m).
  { move/eqP :E (fpredn_lt m) (fpredn_lt y)=>-> ??? /ca_le ? /and5P[]. slia. }
  move/negbT/ca_decr: E => /apply.
  case=> z /andP[C /orP[/double /succ_lt ? /andP[? /eqP-> *]| R]].
  { apply/(IHn z)=> //.
    apply/cfP; exists x, y.
    exact/and3P. }
  move: R C=> /andP[? /eqP<-] ? /ca_trans /(_ ca_fpredn) ? /icf_symm ?. 
  apply/(rff_consist m)/cfP. 
  exists y, x; exact/and3P.
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
Notation compatible_ext f := (relpre (ext f) compatible).
