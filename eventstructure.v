From mathcomp Require Import ssreflect ssrnat ssrfun ssrbool seq fintype order.
From mathcomp Require Import eqtype fingraph path tuple finmap finfun choice.
From event_struct Require Import utilities relations rfsfun wftype.

Import Order.LTheory.
Open Scope order_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Definition var := nat.

Inductive label {Rval Wval : Type} :=
| Read of var & Rval
| Write of var & Wval
| ThreadStart
| ThreadEnd.

Section PrimeEventStructure.

Context {val : eqType}.

(* ************************************************************************* *)
(*     Label                                                                 *)
(* ************************************************************************* *)

Local Notation label := (@label val val).

Implicit Type (l : label).

Definition eq_label l l' := 
  match l, l' with
  | Read a x,  Read b y  | Write a x,   Write b y   => [&& a == b & x == y]
  | ThreadEnd, ThreadEnd | ThreadStart, ThreadStart => true
  | _, _                                           => false
  end.

Lemma eqlabelP : Equality.axiom eq_label.
Proof. 
  case=> [v x [] * /=|v x []* /=|[]|[]]; try constructor=>//;
  by apply: (iffP andP)=> [[/eqP->/eqP->]|[->->]].
Qed.

Canonical label_eqMixin := EqMixin eqlabelP.
Canonical label_eqType := Eval hnf in EqType label label_eqMixin.

Definition is_read  l := if l is (Read _ _) then true else false.

Definition is_thdstart l := if l is ThreadStart then true else false.

Definition write_read_from (w r : label) := 
  match w, r with
  | (Write x a), (Read y b) => (x == y) && (a == b)
  | _, _                    => false
  end.

Notation "w << r" := (write_read_from w r) (at level 0).

(* ************************************************************************* *)
(*     Exec Event Structure                                                  *)
(* ************************************************************************* *)


Structure exec_event_struct (E : wfType) := Pack {
  domain : {fset E};
  lab    : rfsfun (fun=> ThreadEnd) domain (fun _ _ => true);
  ffpred : rfsfun id domain (>=%O : rel E);
  ffrf   : rfsfun id domain 
           [rel r w : E | (w <= r) && ((w == r) (+) ((lab w) << (lab r)))]
}.

Section ExecEventStructure.

Context {E} (es : (exec_event_struct E)).

Notation domain := (domain es).
Notation lab     := (lab es).
Notation ffpred   := (ffpred es).
Notation ffrf     := (ffrf es).

(* ************************************************************************* *)
(*     Event Types                                                           *)
(* ************************************************************************* *)

(* ************************************************************************* *)
(*     Predecessor and Successor                                             *)
(* ************************************************************************* *)

Definition fpred : E -> E := ffpred.

Definition pred e1 e2 := (e1 != e2) && (fpred e1 == e2).

Definition succ e1 e2 := (e1 != e2) && (fpred e2 == e1).

Lemma fpred_lt e: fpred e <= e.
Proof. 
  case I: (e \in domain); first exact (axiom_rfsfun ffpred I).
  by rewrite /fpred (memNdom _ (negbT I)).
Qed.

Lemma frpred_domain e: (e \in domain) = false ->
  fpred e = e.
Proof. by move/negbT/(memNdom ffpred). Qed.


Lemma pred_lt e1 e2 : pred e1 e2 -> e2 < e1.
Proof. 
  case/andP=> /swap /eqP <- N.
  by rewrite lt_def (fpred_lt e1) N.
Qed.

Lemma succ_lt e1 e2 : succ e1 e2 -> e1 < e2.
Proof. 
  case/andP=> /swap /eqP <- N.
  by rewrite lt_def (fpred_lt e2) eq_sym N. 
Qed.

(* ************************************************************************* *)
(*     Reads-From                                                            *)
(* ************************************************************************* *)

Definition frf : E -> E := ffrf.

Lemma frf_lt r : frf r <= r.
Proof.
  case I: (r \in domain); first by case/andP: (axiom_rfsfun ffrf I).
  by rewrite /frf (memNdom _ (negbT I)).
Qed.

(* Reads-From relation *)
Definition rf w r := (w != r) && (frf r == w).

Lemma rf_lt w r : rf w r -> w < r.
Proof. 
  case/andP=> /swap /eqP <- N.
  by rewrite lt_def (frf_lt r) eq_sym N. 
Qed.

Lemma frf_domain e: (e \in domain) = false ->
  frf e = e.
Proof. by move/negbT/(memNdom ffrf). Qed.

(* ************************************************************************* *)
(*     Causality                                                             *)
(* ************************************************************************* *)

(* Immediate causality relation *)
Definition ica : rel E := 
  fun e1 e2 => succ e1 e2 || rf e1 e2.

Lemma ica_lt e1 e2 : ica e1 e2 -> e1 < e2.
Proof. by move /orP=> [/succ_lt | /rf_lt]. Qed.

(* Causality relation *)
Definition ca : rel E. Admitted.

Lemma closureP e1 e2: 
  reflect (closure _ ica e1 e2) (ca e1 e2).
Admitted.

Lemma succ_ca x y : succ x y -> ca x y. Admitted.
(*Proof. move=> ?. apply /irel_rt_cl. by apply /orP; left. Qed.*)

Lemma rf_ca e1 e2 : rf e1 e2 -> ca e1 e2. Admitted.
(*Proof. move=> ?. apply /irel_rt_cl. by apply /orP; right. Qed.*)

Lemma ca_refl: reflexive ca. Admitted.
(*Proof. exact: rt_cl_refl. Qed.*)

Lemma ca_trans: transitive ca. Admitted.
(*Proof. exact: rt_cl_trans. Qed. *)

Arguments ca_trans {_ _ _}.

Lemma ca_decr e1 e2 : e1 != e2 -> ca e1 e2 ->
  exists e3, ca e1 e3 && ica e3 e2. 
Proof.
  move /swap/closureP=> [/eqP // | e3 e4 ?].
  move=> /closureP E' *.
  exists e3. by rewrite E'. 
Qed.

Lemma ca_le e1 e2 : ca e1 e2 -> e1 <= e2.
Proof. 
  move/closureP.
  by elim=> [] // ??/ica_lt /ltW L ? /le_trans /(_ L).
Qed.

Lemma ca_anti: antisymmetric ca.
Proof. 
  move=> x y /andP[/ca_le Eq /ca_le ?]. 
  by rewrite (@le_anti _ _ x y) // Eq.
Qed.

Lemma ca_fpredn {e}: ca (fpred e) e.
Proof.
  case Eq: (fpred e != e); last (move/eqP: Eq->; by rewrite ca_refl).
  by rewrite succ_ca // /succ eq_refl Eq.
Qed.

Lemma ca_frfn e : ca (frf e) e.
Proof.
  case Eq: (frf e != e); last (move/eqP: Eq->; by rewrite ca_refl).
  by rewrite rf_ca // /rf eq_refl Eq.
Qed.

Lemma ica_codom e1 e2: ica e1 e2 -> (e2 \in domain).
Proof.
  case D: (e2 \in domain)=> //; move: D=>/dup /frf_domain /swap /frpred_domain.
  by rewrite /ica /succ /rf =>->-> /orP[] /andP[/negP /swap /eqP->].
Qed.

Lemma ca_codom e1 e2: ca e1 e2 -> (e2 \in domain) = false ->
  (e1 == e2).
Proof.
  move/closureP; elim; first by rewrite eq_refl.
  by move=> ?? /swap ? /ica_codom->.
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
Canonical predorderType := POrderType ev_display E orderMixin.

Notation "x <c= y" := (@Order.le ev_display _ x y) (at level 0).

(* ************************************************************************* *)
(*     Conflict                                                              *)
(* ************************************************************************* *)

(* Immediate conflict relation *)
Definition icf (e1 e2 : E) :=
  [&& (e1 != e2),
      fpred e1 == fpred e2,
      fpred e1 < e1,
      fpred e2 < e2,
      ~~ is_thdstart (lab e1) &
      ~~ is_thdstart (lab e2)].

Lemma icf_symm e1 e2: icf e1 e2 -> icf e2 e1.
Proof. 
  case/and5P=>*. 
  by apply/and5P; split=> //; rewrite 1?eq_sym // andbC.
Qed.

Definition seqpred_ca (e1 : E) : seq E. Admitted.

Lemma seqpred_ca_in e1 e2: e1 \in seqpred_ca e2 = ca e1 e2.
Proof. Admitted.

(* Conflict relation *)
Definition cf e1 e2 :=
  has (fun x => (has (icf x) (seqpred_ca e2))) (seqpred_ca e1).

Notation "a # b" := (cf a b) (at level 10).

Lemma cfP {e1 e2}:
  reflect (exists e1' e2', [&& ca e1' e1, ca e2' e2 & icf e1' e2']) (e1 # e2).
Proof.
  apply/(iffP hasP)=> [[x /swap /hasP [y]]|[x [y /and3P[]]]].
  { rewrite 2!seqpred_ca_in=> *.
    exists x, y.
    exact /and3P. }
  rewrite -2!seqpred_ca_in=> *.
  exists x=> //.
  apply /hasP. 
  by exists y.
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
  (ffpred e1) # e2,  e1 # (fpred e2),
  (ffrf   e1) # e2 | e1 # (ffrf  e2)].

Lemma cf_step_cf e1 e2: cf_step e1 e2 -> e1 # e2.
Proof.
  move/or4P => [|||/orP[]] => H.
  { apply/cfP; exists e1, e2.
    by rewrite !ca_refl. }
  all: apply/(consist_cf H)=> //; by rewrite ?ca_refl ?ca_fpredn ?ca_frfn.
Qed.

Lemma cfE e1 e2: e1 # e2 = cf_step e1 e2.
Proof.
  apply /(sameP idP)/(iffP idP)=> [/cf_step_cf | /cfP] //.
  case=> ? [? /and3P[/closureP]].
  elim=> [/closureP |].
  { elim=> [-> |] //.
    by move=> ?? /orP[]/andP[?] /eqP<- /closureP ? H /H /cf_step_cf->. }
  by move=> ?? /orP[]/andP[?] /eqP<-/closureP ? IH L /(IH L) /cf_step_cf->.
Qed.

(* ************************************************************************* *)
(*     Reads-From Consistency                                                *)
(* ************************************************************************* *)

Definition consistency := [forall e : domain, ~~ (fsval e) # (frf (fsval e))].

Hypothesis consist : consistency.

Lemma rff_consist e : ~ e # (frf e).
Proof.
  case D: (e \in domain).
  { rewrite -[e]/(fsval [` D]%fset). 
    apply/negP; by move/forallP: consist. }
  rewrite frf_domain // => /cfP[? [? /and3P[/ca_codom/(_ D) /eqP ->]]].
  by move/ca_codom/(_ D)/eqP-> => /andP[/negP].
Qed.

Lemma cf_irrelf : irreflexive cf.
Proof.
  move=> m; apply/negbTE/negP.
  elim/(@wf_ind E): m=> m IHn.
  suff C: ~ m # (fpred m).
  { rewrite cfE=> /or4P[|||/orP[]] //.
    1-3: rewrite /icf (eq_refl, cf_symm) //.
    all: exact/rff_consist. }
  move=> /cfP[x [y /and3P[]]]; case Eq: (x == m).
  { move/eqP :Eq =>-> ? /ca_le L /and5P[?/eqP<- ?] /(le_lt_trans L).
    by rewrite ltxx. }
  move/negbT/ca_decr: Eq => /apply.
  case=> z /andP[C /orP[/dup /succ_lt ? /andP[? /eqP-> *]| R]].
  { apply/(IHn z)=> //.
    apply/cfP; exists x, y; exact/and3P. }
  move: R C=> /andP[? /eqP<-] ? /ca_trans /(_ ca_fpredn) ? /icf_symm ?. 
  apply/(@rff_consist m)/cfP. 
  exists y, x; exact/and3P.
Qed.

End ExecEventStructure.

Section Consistency.

Context {E : wfType}.
Implicit Type es : (@exec_event_struct E).

Inductive cexec_event_struct := Consist es of (consistency es).

Arguments Consist {_}.

Coercion ev_struct_of (ces : cexec_event_struct) :=
  let '(Consist es _) := ces in es.

Canonical consist_subType := [subType for ev_struct_of].

Lemma consist_inj : injective (ev_struct_of).
Proof. exact: val_inj. Qed.

End Consistency.

End PrimeEventStructure.

Notation "x <=c y" := (@Order.le ev_display _ x y) (at level 10).
Notation "a # b" := (cf _ a b) (at level 10).