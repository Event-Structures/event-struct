From Coq Require Import Relations.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq path.
From mathcomp Require Import eqtype choice order finmap.
From event_struct Require Import utilities relations rfsfun wftype ident.

(******************************************************************************)
(* This file contains the definitions of:                                     *)
(*     fin_exec_event_structure d E == definition of finite execution event   *)
(*                              structure where E : identType d               *)
(*           label R W == label that can be: Read x a, Write x a, ThreadEnd   *)
(*                      or ThreadStart                                        *)
(*           w << r == r can read from w                                      *)
(* --> it_contains:                                                           *)
(*          1) dom : seq E == all elements of our event structure. It should  *)
(*                   by sorted because we want to create a fresh element,     *)
(*                   that is not in dom just by taking fresh of it's biggest  *)
(*                   element                                                  *)
(*          2) lab : rfsfun (fun=> ThreadEnd) dom (fun _ _ => true)           *)
(*                    == labeling finite function on dom, that returns        *)
(*                   ThreadEnd if out of domain                               *)
(*          3) ffpred : rfsfun id dom (>=%O) == finite function that returns  *)
(*                  predsessor of arbitrary element x if he has one, or x     *)
(*                  otherwise                                                 *)
(*          4) ffrf   :                                                       *)
(*             rfsufn id dom                                                  *)
(*             [rel r w : E | (w <= r) && ((w == r) (+) ((lab w) << (lab r)))]*)
(*             == finite function that by x returns element form that x reads *)
(*              if lab x = Read and x otherwise                               *)
(* Then we are trying to derive some theory of finite event structure:        *)
(*               ica x y iff x = ffred y or x = ffrf y                        *)
(*               ca == casuality relation (just reflexive-transitive closure  *)
(*                  of ica                                                    *)
(*               cf == conflict relation (e1 # e2 -- notation for cf e1 e2)   *)
(* If we ask that reads are not in conflict with the writes where they read   *)
(* from, we can prove irreflexivity of our conflict relation.                 *)
(* So we can define:                                                          *)
(*             cexec_event_structure == subtype of fin_exec_event_structure   *)
(*                where reads and corresponding writes are conflict-free and  *)
(*                thus conflict relation is irreflexive                       *)
(******************************************************************************)

Import Order.LTheory.
Open Scope order_scope.


Set Implicit Arguments.
Unset Strict Implicit.

Definition loc := nat.

Inductive label {Rval Wval : Type} :=
| Read of loc & Rval
| Write of loc & Wval
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
  dom        : seq E;
  dom_sorted : sorted (>%O) dom;
  lab        : rfsfun (fun=> ThreadEnd) dom (fun _ _ => true);
  ffpred     : rfsfun id dom (>=%O : rel E);
  ffrf       : rfsfun id dom
               [rel r w : E | (w <= r) &&
               (((w == r) && ~~ is_read (lab r)) || ((lab w) << (lab r)))]
}.

Section ExecEventStructure.

Context {disp} {E : identType disp} (es : (fin_exec_event_struct E)).

Notation domain := (dom es).
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

Lemma fica_domain e: (e \in domain) = false ->
  fica e = [:: e; e].
Proof. by move/negbT/[dup]/(memNdom ffpred)=> {4}<- /(memNdom ffrf) {2}<-. Qed.

Lemma fica_le e1 e2: e1 \in (fica e2) -> e1 <= e2.
Proof. rewrite ?inE=> /orP[]/eqP->; by rewrite (frf_le, fpred_le). Qed.

(* ************************************************************************* *)
(*     Causality                                                             *)
(* ************************************************************************* *)

(* Immediate causality relation *)
Definition ica e1 e2: bool := e1 \in fica e2.

Arguments ica /.

Lemma ica_le e1 e2 : ica e1 e2 -> e1 <= e2.
Proof. by move/fica_le. Qed.

Arguments clos_rtn1_rt {_ _ _ _}.
Arguments clos_rt_rt1n {_ _ _ _}.
Arguments clos_rt_rtn1 {_ _ _ _}.
Arguments clos_rt1n_rt {_ _ _ _}.

(* Causality relation *)
Definition ca : rel E := rt_closure fica fica_le.

Lemma closureP e1 e2: 
  reflect (clos_refl_trans_n1 _ ica e1 e2) (ca e1 e2).
Proof. exact/(equivP (rt_closure_n1P _ _ _ _)). Qed.

Lemma fica_ca e1 e2: e1 \in fica e2 -> ca e1 e2.
Proof. 
  move=> H. apply/closureP/(Relation_Operators.rtn1_trans); first exact: H.
  exact: rtn1_refl.
Qed.

Lemma ca_refl: reflexive ca.
Proof. exact: rt_closure_refl. Qed.

Lemma ca_trans: transitive ca. 
Proof. move=>???. exact: rt_closure_trans. Qed.

Arguments ca_trans {_ _ _}.

Lemma ca_le e1 e2 : ca e1 e2 -> e1 <= e2.
Proof. 
  move/closureP.
  by elim=> [] // ??/ica_le L ? /le_trans /(_ L).
Qed.

Lemma ca_decr e1 e2 : e1 != e2 -> ca e1 e2 ->
  exists e3, [&& ca e1 e3, ica e3 e2 & e3 < e2]. 
Proof.
  move/[swap]/closureP/clos_rtn1_rt/clos_rt_rt1n; elim=> [?/eqP//|].
  move=> x y z I /clos_rt1n_rt/clos_rt_rtn1/closureP L.
  case N: (y != z). 
  - case/(_ erefl)=> e /and3P[C *]; exists e; apply/and3P; split=> //.
    exact/(ca_trans _ C)/fica_ca.
  move/eqP: N I L=> -> I ?? N; exists x.
  by rewrite ca_refl I /= lt_def eq_sym N /= ica_le.
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

Lemma ca_codom e1 e2: ca e1 e2 -> (e2 \in domain) = false ->
  (e1 == e2).
Proof. 
  move/closureP; elim=> //?? I ? Y Z; move: I Y.
  by rewrite /ica fica_domain // ?inE orbb=> /eqP-> /(_ Z).
Qed.

(*Lemma ca_dom e1 e2: ca e1 e2 -> (e1 \in domain) = false ->
  e1 = e2.
Proof.
  move/closureP; elim=> // x y I /closureP ? IH /[dup]/IH.
  move: I=> /[swap] .
Qed.*)


(* Strict (irreflexive) causality *)
(*Definition sca e1 e2 := (e2 != e1) && (ca e1 e2).

Lemma sca_def : forall e1 e2, sca e1 e2 = (e2 != e1) && (ca e1 e2).
Proof. done. Qed.

Definition orderMixin :=
  LePOrderMixin sca_def ca_refl ca_anti (@ca_trans).

Definition ev_display : unit.
Proof. exact: tt. Qed.

(* TODO: make this canonocal projection work *)
Canonical predorderType := POrderType ev_display E orderMixin.

Notation "x <c= y" := (@Order.le ev_display _ x y) (at level 0).*)

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

Definition seqpred_ca := up_set fica fica_le .

Lemma seqpred_ca_in e1 e2: e1 \in seqpred_ca e2 = ca e1 e2.
Proof. by []. Qed.

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
  case/or3P=> [/icf_cf||]// /hasP[? /fica_ca /[swap] /consist_cf /[apply]];
  last rewrite cf_symm; apply; by rewrite ca_refl.
Qed.

Lemma cfE e1 e2: e1 # e2 = cf_step e1 e2.
Proof.
  apply /(sameP idP)/(iffP idP)=> [/cf_step_cf | /cfP] //.
  case=> ? [? /and3P[/closureP]].
  elim=> [/closureP | ?? /[swap] ?].
  - elim=> [-> |] // ?? /[swap] _.
    rewrite /ica ?inE=> /orP[]/eqP-> /[apply] /cf_step_cf /= -> //=;
    by rewrite orbT.
  rewrite /ica ?inE=> /orP[]/eqP-> /[apply]/[apply] /cf_step_cf /=;
  by rewrite cf_symm=> /= ->.
Qed.

(* ************************************************************************* *)
(*     Reads-From Consistency                                                *)
(* ************************************************************************* *)

Definition consistency :=  all (fun e => ~~ e # (frf e)) domain.

Hypothesis consist : consistency.

Lemma rff_consist e : ~ e # (frf e).
Proof.
  case D: (e \in domain).
  - apply/negP; by move/allP/(_ _ D): consist.
  rewrite frf_domain // => /cfP[? [? /and3P[/ca_codom/(_ D) /eqP ->]]].
  by move/ca_codom/(_ D)/eqP-> => /andP[/negP].
Qed.

Lemma cf_irrelf : irreflexive cf.
Proof.
  move=> m; apply/negbTE/negP.
  elim/(@wfb_ind disp E): m=> m IHn.
  suff C: ~ m # (fpred m).
  - by rewrite cfE /icf=> /or3P[/andP[/eqP]||] //= /or3P[]// /rff_consist.
  move=> /cfP[x [y /and3P[]]]; case Eq: (x == m).
  - move/eqP :Eq =>-> ? /ca_le L /and5P[?/eqP<- ?] /(le_lt_trans L).
    by rewrite ltxx.
  move/negbT/ca_decr: Eq => /[apply] [[z /and3P[/[swap]]]].
  rewrite /ica=> /or3P[]// /eqP-> C1 ?.
  - move/ca_trans /(_ ca_fpred)=> ? /icf_cf; rewrite cf_symm=> C. 
    exact/(@rff_consist m)/(consist_cf C).
  move=> C2 /icf_cf /consist_cf/(_ C1 C2); exact/IHn.
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

(*Notation "x <c= y" := (@Order.le ev_display _ x y) (at level 10).*)
Notation "a # b" := (cf _ a b) (at level 10).
Notation "w << r" := (write_read_from w r) (at level 0). 
