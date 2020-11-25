From mathcomp Require Import ssreflect ssrnat ssrfun ssrbool seq fintype order.
From mathcomp Require Import eqtype fingraph path tuple finmap finfun choice.
From event_struct Require Import utilities relations rfsfun wftype ident.
From Coq Require Import ssrsearch.

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
  | Read a x,  Read b y      => [&& a == b & x == y]
  | Write a x, Write b y     => [&& a == b & x == y]
  | ThreadEnd, ThreadEnd     => true
  | ThreadStart, ThreadStart => true
  | _, _                     => false
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


Structure fin_exec_event_struct {disp} (E : identType disp) := Pack {
  N      : nat;
  lab    : rfsfun (fun=> ThreadEnd) (nfresh_set N) (fun _ _ => true);
  ffpred : rfsfun id (nfresh_set N) (>=%O : rel E);
  ffrf   : rfsfun id (nfresh_set N)
           [rel r w : E | (w <= r) && ((w == r) (+) ((lab w) << (lab r)))]
}.

Section ExecEventStructure.

Context {disp} {E : identType disp} (es : (fin_exec_event_struct E)).

Notation N := (N es).
Notation domain := (nfresh_set N).
Notation lab     := (lab es).
Notation ffpred   := (ffpred es).
Notation ffrf     := (ffrf es).

(* ************************************************************************* *)
(*     Event Types                                                           *)
(* ************************************************************************* *)

(* ************************************************************************* *)
(*     Predecessor                                                           *)
(* ************************************************************************* *)

Definition fpred : E -> E := ffpred.

Lemma fpred_le e: fpred e <= e.
Proof. 
  case I: (e \in domain); first exact (axiom_rfsfun ffpred I).
  by rewrite /fpred (memNdom _ (negbT I)).
Qed.

(* ************************************************************************* *)
(*     Reads-From                                                            *)
(* ************************************************************************* *)

Definition frf : E -> E := ffrf.

Lemma frf_le r : frf r <= r.
Proof.
  case I: (r \in domain); first by case/andP: (axiom_rfsfun ffrf I).
  by rewrite /frf (memNdom _ (negbT I)).
Qed.

Lemma frf_domain e: (e \in domain) = false ->
  frf e = e.
Proof. by move/negbT/(memNdom ffrf). Qed.

Definition fica e := [:: frf e; fpred e].
Definition fsica e := [seq x <- fica e | x != e].

Arguments fsica /.

Lemma fica_domain e: (e \in domain) = false ->
  fica e = [:: e; e].
Proof. by move/negbT/dup/(memNdom ffpred)=> {4}<- /(memNdom ffrf) {2}<-. Qed.

Lemma fsica_lt e1 e2: e1 \in (fsica e2) -> e1 < e2.
Proof. 
  rewrite mem_filter lt_def eq_sym ?inE=>/andP[-> /orP[]/eqP->];
  by rewrite (frf_le, fpred_le).
Qed.

(* ************************************************************************* *)
(*     Causality                                                             *)
(* ************************************************************************* *)

(* Immediate causality relation *)
Definition ica e1 e2: bool := e1 \in fsica e2.

Arguments ica /.

Lemma ica_lt e1 e2 : ica e1 e2 -> e1 < e2.
Proof. by move/fsica_lt. Qed.

(* Causality relation *)
Definition ca : rel E. Admitted.

Lemma closureP e1 e2: 
  reflect (closure _ ica e1 e2) (ca e1 e2).
Admitted.

Lemma fica_ca e1 e2: e1 \in fica e2 -> ca e1 e2.
Proof. Admitted.

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

Lemma ca_fpred {e}: ca (fpred e) e.
Proof.
  case Eq: (fpred e != e); last (move/eqP: Eq->; by rewrite ca_refl).
  by apply/fica_ca; rewrite ?inE eq_refl.
Qed.

Lemma ica_codom e1 e2: ica e1 e2 -> (e2 \in domain).
Proof.
  case D: (e2 \in domain)=> //; move: D=> /fica_domain.
  by rewrite /ica mem_filter =>->; rewrite ?inE orbb andNb.
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
  has (fun p=> icf p.1 p.2)
  (allpairs pair (seqpred_ca e1) (seqpred_ca e2)).

Notation "a # b" := (cf a b) (at level 10).

Lemma cfP {e1 e2}:
  reflect (exists e1' e2', [&& ca e1' e1, ca e2' e2 & icf e1' e2']) (e1 # e2).
Proof.
  apply/(iffP hasP)=> [[? /allpairsPdep[x[y[]]]]|[x [y /and3P[]]]].
  - rewrite 2!seqpred_ca_in=> ?? -> /= ?.
    exists x, y; exact /and3P.
  rewrite -2!seqpred_ca_in=> *.
  exists (x, y)=> //; exact /allpairs_f. 
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
      has (cf e1) (fica e2) |
      has (cf e2) (fica e1)].

Lemma icf_cf e1 e2: icf e1 e2 -> e1 # e2.
Proof.
  move=> I; apply/cfP.
  exists e1, e2; by rewrite ?ca_refl I.
Qed.

Lemma cf_step_cf e1 e2: cf_step e1 e2 -> e1 # e2.
Proof.
  case/or3P=> [/icf_cf||]// /hasP[? /fica_ca /swap /consist_cf /apply];
  last rewrite cf_symm; apply; by rewrite ca_refl.
Qed.

Lemma cfE e1 e2: e1 # e2 = cf_step e1 e2.
Proof.
  apply /(sameP idP)/(iffP idP)=> [/cf_step_cf | /cfP] //.
  case=> ? [? /and3P[/closureP]].
  elim=> [/closureP | ?? /swap ?].
  - elim=> [-> |] // ?? /swap _.
    rewrite /ica mem_filter ?inE => /andP[?/orP[] /eqP->] /apply /cf_step_cf;
    move=> /= ->; by rewrite orbT.
  rewrite /ica mem_filter ?inE => /andP[? /orP[] /eqP->] /apply/apply;
  move/cf_step_cf; by rewrite cf_symm=> /= ->.
Qed.

(* ************************************************************************* *)
(*     Reads-From Consistency                                                *)
(* ************************************************************************* *)

Definition consistency := [forall e : domain, ~~ (fsval e) # (frf (fsval e))].

Hypothesis consist : consistency.

Lemma rff_consist e : ~ e # (frf e).
Proof.
  case D: (e \in domain).
  - rewrite -[e]/(fsval [` D]%fset). 
    apply/negP; by move/forallP: consist.
  rewrite frf_domain // => /cfP[? [? /and3P[/ca_codom/(_ D) /eqP ->]]].
  by move/ca_codom/(_ D)/eqP-> => /andP[/negP].
Qed.

Lemma cf_irrelf : irreflexive cf.
Proof.
  move=> m; apply/negbTE/negP.
  elim/(@wf_ind disp E): m=> m IHn.
  suff C: ~ m # (fpred m).
  - by rewrite cfE /icf=> /or3P[/andP[/eqP]||] //= /or3P[]// /rff_consist.
  move=> /cfP[x [y /and3P[]]]; case Eq: (x == m).
  - move/eqP :Eq =>-> ? /ca_le L /and5P[?/eqP<- ?] /(le_lt_trans L).
    by rewrite ltxx.
  move/negbT/ca_decr: Eq => /apply.
  case=> z /andP[/swap]. rewrite /ica mem_filter ?inE=> /andP[/swap /orP[|]].
  - move/eqP->=> ?? /ca_trans /(_ ca_fpred) ? /icf_cf; rewrite cf_symm=> C. 
    exact/(@rff_consist m)/(consist_cf C).
  move/eqP->=> N C1 C2 /icf_cf /consist_cf/(_ C1 C2). 
  by apply/IHn; rewrite lt_def eq_sym N fpred_le.
Qed.

End ExecEventStructure.

Section Consistency.

Context {disp}{E : identType disp}.
Implicit Type es : (@fin_exec_event_struct disp E).

Inductive cexec_event_struct := Consist es of (consistency es).

Arguments Consist {_}.

Coercion ev_struct_of (ces : cexec_event_struct) :=
  let '(Consist es _) := ces in es.

Canonical consist_subType := [subType for ev_struct_of].

Lemma consist_inj : injective (ev_struct_of).
Proof. exact: val_inj. Qed.

End Consistency.

End PrimeEventStructure.

Notation "x <c= y" := (@Order.le ev_display _ x y) (at level 10).
Notation "a # b" := (cf _ a b) (at level 10).