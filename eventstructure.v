From Coq Require Import Relations Relation_Operators.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq path.
From mathcomp Require Import eqtype choice order finmap.
From event_struct Require Import utilities relations wftype ident.

(******************************************************************************)
(* This file contains the definitions of:                                     *)
(* Event labels:                                                              *)
(*   label R W == an event label telling its type: read, write, the start of  *)
(*                of a thread or the end of a thread                          *)
(*      w << r == an event labelled `r` reads from an event labelled `w`      *)
(*                                                                            *)
(* Finite execution event structures:                                         *)
(*   fin_exec_event_structure d E == definition of a finite execution event   *)
(*                                   structure where E : identType d          *)
(*     dom == the sorted sequences of events of the event structure. It is    *)
(*            sorted in the descending order to make issuing fresh events     *)
(*            a constant time operation.                                      *)
(*   lab e == the label of the event e; lab is a finitely supported function  *)
(*            defined on dom; returns ThreadEnd for the events outside of     *)
(*            dom.                                                            *)
(* fpred e == the predecessor of the event e, fpred is a finitely supported   *)
(*            function that returns e if e is outside of dom.                 *)
(*   frf e == finite function that by x returns element form that x reads     *)
(*              if lab x = Read and x otherwise                               *)
(* ica x y == x is the predecessor of y or y reads from x, ica stands for     *)
(*            immediate causality relation.                                   *)
(*      ca == non-strict casuality relation, i.e. the reflexive-transitive    *)
(*              closure of ica.                                               *)
(* e1 # e2 == e1 and e2 are conflicting events.                               *)
(*                                                                            *)
(* One can prove irreflexivity of the conflict relation under the assumption  *)
(* that reads are not in conflict with the writes they read from:             *)
(*   cexec_event_structure == a subtype of finite execution event structures  *)
(*                            with irreflexive conflict relation              *)
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

Context {V : eqType}.

(* ************************************************************************* *)
(*     Label                                                                 *)
(* ************************************************************************* *)

Local Notation label := (@label V V).

Implicit Type l : label.

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

(* label location *)
Definition lloc (l : label) :=
  match l with
  | Write x _ => Some x
  | Read  x _ => Some x
  | _         => None
  end.

Definition is_read l := if l is (Read _ _) then true else false.

Definition is_write l := if l is Write _ _ then true else false.

Definition is_thdstart l := if l is ThreadStart then true else false.

Definition write_read_from (w r : label) :=
  match w, r with
  | Write x a, Read y b => (x == y) && (a == b)
  | _, _ => false
  end.

Notation "w << r" := (write_read_from w r) (at level 0).

Lemma rf_thrdend w : w << ThreadEnd = false.
Proof. by case: w. Qed.


(* ************************************************************************* *)
(*     Exec Event Structure                                                  *)
(* ************************************************************************* *)

Structure fin_exec_event_struct {disp} (E : identType disp) := Pack {
  dom        : seq E;
  dom_sorted : sorted (>%O) dom;
  (* lprf stands for label, predecessor, reads-from *)
  lprf       : {fsfun for fun e => (ThreadEnd, e, e)};
  lab e      := (lprf e).1.1;  (* lab is 1st projection *)
  fpred e    := (lprf e).1.2;  (* fpred is 2nd projection *)
  frf e      := (lprf e).2;    (* frf is 3d projection *)
  _          : {subset (finsupp lprf) <= dom};
  _          : forall e : E, fpred e <= e;
  _          : forall r : E, let w := frf r in
                 (w <= r) &&
                 (((w == r) && ~~ is_read (lab r)) || ((lab w) << (lab r)));
}.

Section ExecEventStructure.

Context {disp} {E : identType disp} (es : fin_exec_event_struct E).

Notation dom := (dom es).
Notation lprf := (lprf es).
Notation lab := (lab es).
Notation fpred := (fpred es).
Notation frf := (frf es).

Lemma labE e : lab e = (lprf e).1.1.
Proof. by []. Qed.

Lemma fpredE e : fpred e = (lprf e).1.2.
Proof. by []. Qed.

Lemma frfE e : frf e = (lprf e).2.
Proof. by []. Qed.


Lemma lprf_dom : {subset (finsupp lprf) <= dom}.
Proof. by case: es. Qed.

(***** Labels and Freshness *****)
Section LabelsFresh.

Notation fresh_id := (fresh_seq dom).

Lemma lab_fresh : lab fresh_id = ThreadEnd.
Proof.
  rewrite /lab fsfun_dflt //; apply/negP=> /lprf_dom; apply/negP.
  by rewrite fresh_seq_notin ?dom_sorted.
Qed.

End LabelsFresh.

(* ************************************************************************* *)
(*     Predecessor                                                           *)
(* ************************************************************************* *)

Lemma fpred_le e : fpred e <= e.
Proof. by case: es. Qed.

Lemma fpred_dom e :
  e \notin dom -> fpred e = e.
Proof.
  move=> ndom; rewrite /fpred fsfun_dflt //; move: ndom.
  by apply/contra/lprf_dom.
Qed.

(* ************************************************************************* *)
(*     Reads-From                                                            *)
(* ************************************************************************* *)

Lemma frf_cond r : let w := frf r in
  (w <= r) &&
  (((w == r) && ~~ is_read (lab r)) || ((lab w) << (lab r))).
Proof. by case: es. Qed.

Lemma frf_le r : frf r <= r.
Proof. by case/andP: (frf_cond r). Qed.

Lemma frf_lt {e1 e2} : e1 < e2 -> frf e1 < e2.
Proof. by apply/le_lt_trans/frf_le. Qed.

Lemma frf_dom e :
  e \notin dom -> frf e = e.
Proof.
  move=> ndom; rewrite /frf fsfun_dflt //; move: ndom.
  by apply/contra/lprf_dom.
Qed.

Definition fica e := [:: frf e; fpred e].

Lemma fica_dom e :
  e \notin dom -> fica e = [:: e; e].
Proof. by move=> nI; rewrite /fica frf_dom // fpred_dom. Qed.

Lemma fica_le e1 e2: e1 \in fica e2 -> e1 <= e2.
Proof. rewrite ?inE=> /orP[]/eqP->; by rewrite (frf_le, fpred_le). Qed.

(* ************************************************************************* *)
(*     Causality                                                             *)
(* ************************************************************************* *)

(* Immediate causality relation *)
Definition ica e1 e2 : bool := e1 \in fica e2.

Lemma ica_le e1 e2 : ica e1 e2 -> e1 <= e2.
Proof. exact: fica_le. Qed.

(* Causality relation *)
Definition ca : rel E := rt_closure fica fica_le.

Lemma closureP e1 e2 :
  reflect (clos_refl_trans_n1 ica e1 e2) (ca e1 e2).
Proof. exact/(equivP rt_closure_n1P). Qed.

Lemma ica_ca e1 e2 : ica e1 e2 -> ca e1 e2.
Proof. exact: rt_closure_subrel. Qed.

Lemma ica_fpred {e}: ica (fpred e) e.
Proof. by rewrite /ica !inE eqxx. Qed.

Lemma ica_notdom e1 e2:
  e2 \notin dom ->
  ica e1 e2 ->
  e1 == e2.
Proof. by move=> Ndom2; rewrite /ica fica_dom // !inE orbb. Qed.

Lemma ca_refl {e} : ca e e.
Proof. exact: rt_closure_refl. Qed.

Hint Resolve ca_refl : core.

Lemma ca_trans: transitive ca.
Proof. exact: rt_closure_trans. Qed.

Arguments ca_trans {_ _ _}.

Lemma ca_anti: antisymmetric ca.
Proof. exact: rt_closure_antisym. Qed.

Lemma ca_le e1 e2 : ca e1 e2 -> e1 <= e2.
Proof. exact: rt_closure_le. Qed.

Lemma ca_step_last e1 e3 :
  e1 != e3 ->
  ca e1 e3 ->
  exists e2, [&& ca e1 e2, ica e2 e3 & e2 < e3].
Proof.
  move/[swap]/closureP; elim=> [/eqP//|] e2 {}e3.
  case: (eqVneq e2 e3)=> [-> _ //| neq23 I23 /closureP C12 _ neq13].
  by exists e2; rewrite C12 I23 lt_neqAle neq23 ica_le.
Qed.

Lemma ca_fpredl {e} : ca (fpred e) e.
Proof. exact/ica_ca/ica_fpred. Qed.

Lemma ca_fpredr e1 e2 : ca e1 (fpred e2) -> ca e1 e2.
Proof. by move/ca_trans/(_ ca_fpredl). Qed.

Lemma ca_notdom e1 e2:
  ca e1 e2 -> e2 \notin dom ->
  e1 == e2.
Proof.
  move/closureP; elim=> // {}e2 e3 + _ + N3.
  by move=> /(ica_notdom N3) /eqP-> /(_ N3).
Qed.

Definition seqpred_ca := up_set fica fica_le.

Lemma seqpred_ca_in e1 e2: e1 \in seqpred_ca e2 = ca e1 e2.
Proof. by []. Qed.

(***** Causality and Freshness *****)
Section CausalityFresh.

Notation fresh_id := (fresh_seq dom).

Lemma ica_fresh e: ica fresh_id e -> e = fresh_id.
Proof.
  move/[dup]/ica_ca/ca_notdom/[swap]/fica_le.
  rewrite /ica ?inE.
  case I: (e \in dom); last by move=> ?/(_ erefl)/eqP->.
  by move/lt_geF: (fresh_seq_lt (dom_sorted es) I)=>->.
Qed.

Lemma ca_fresh e: ca fresh_id e -> e = fresh_id.
Proof. by move/closureP; elim=> // ?? /[swap] ? /[swap]-> /ica_fresh. Qed.

Lemma ca_fresh2 e1 e2 :
  ca e1 e2 -> e1 = fresh_id -> e2 = fresh_id.
Proof. by move/[swap]->; apply: ca_fresh. Qed.

Lemma ca_fresh_contra e1 e2 :
  e2 != fresh_id -> ca e1 e2 -> e1 != fresh_id.
Proof. by move=> nfr2 /ca_fresh2/contra_neq->. Qed.

End CausalityFresh.

(*Lemma ca_dom e1 e2: ca e1 e2 -> (e1 \in dom) = false ->
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
Definition icf (e1 e2 : E) : bool :=
  [&& e1 != e2,
      fpred e1 == fpred e2,
      fpred e1 < e1,
      fpred e2 < e2,
      ~~ is_thdstart (lab e1) &
      ~~ is_thdstart (lab e2)].

Lemma icfxx x : icf x x = false.
Proof. by apply/and6P; case; rewrite eq_refl. Qed.

Definition icf_irrefl : irreflexive icf := icfxx.

Hint Resolve icfxx : core.

Lemma icf_sym : symmetric icf.
Proof.
  by move=> e1 e2; apply/and6P/and6P; case=>*; split=> //; rewrite 1?eq_sym.
Qed.

(* Conflict relation *)
Definition cf e1 e2 : bool :=
  has id [seq icf x y | x <- seqpred_ca e1, y <- seqpred_ca e2].

Notation "a # b" := (cf a b) (at level 10).

Lemma cfP {e1 e2} :
  reflect (exists e1' e2', (ca e1' e1 * ca e2' e2 * icf e1' e2')%type) (e1 # e2).
Proof.
  apply/(iffP hasP)=> [[? /allpairsPdep[x[y[]]]]|[x [y [[]]]]].
  - by rewrite 2!seqpred_ca_in=> ?? -> /= ?; exists x, y.
    by exists (icf x y)=> //; rewrite allpairs_f.
Qed.

Lemma cf_sym: symmetric cf.
Proof.
  apply: symmetric_from_pre=> e1 e2 /cfP [e1' [e2'] Cf].
  by apply/cfP; exists e2', e1'; rewrite icf_sym !Cf.
Qed.

Lemma cf_consist2 e1 e2 e3 e4 :
  e1 # e2 -> ca e1 e3 -> ca e2 e4 -> e3 # e4.
Proof.
  move=> /cfP[e1' [e2'] [[/ca_trans C1] /ca_trans C2 *]].
  by apply/cfP; exists e1', e2'; rewrite C1 // C2.
Qed.

Lemma cf_consistl e1 e2 e3 :
  ca e1 e3 -> e1 # e2 -> e2 # e3.
Proof. by move=> C13 /cf_consist2 /(_ C13); rewrite cf_sym=>->. Qed.

Lemma cf_consistr e1 e2 e3 :
  ca e2 e3 -> e1 # e2 -> e1 # e3.
Proof. by rewrite cf_sym; apply: cf_consistl. Qed.

Lemma icf_cf e1 e2: icf e1 e2 -> e1 # e2.
Proof. by move=> I; apply/cfP; exists e1, e2; rewrite !ca_refl I. Qed.

Notation cf_step e1 e2 :=
  [|| icf e1 e2,
      has (cf e1) (fica e2) |
      has (cf e2) (fica e1)].

Lemma cf_step_cf e1 e2: cf_step e1 e2 -> e1 # e2.
Proof.
  case/or3P=> [/icf_cf //||] /hasP[e /ica_ca]; first by apply: cf_consistr.
  by move=> /cf_consistr /[apply]; rewrite cf_sym.
Qed.

Lemma cfE e1 e2: e1 # e2 = cf_step e1 e2.
Proof.
  apply/idP/idP; last by apply: cf_step_cf.
  case/cfP=> e1' [e2' [[/closureP]]].
  elim=> [/closureP |?? /[swap] _ I /[apply]/[apply]/cf_step_cf].
  - elim=> [-> //| ?? I _ /[apply] /cf_step_cf].
    by move: I; rewrite /ica !inE=> /pred2P[]-> /= ->; rewrite orbT.
  by move: I; rewrite cf_sym /ica ?inE=> /pred2P[]-> /= ->.
Qed.

(* ************************************************************************* *)
(*     Reads-From Consistency                                                *)
(* ************************************************************************* *)

Definition dom_consistency :=  all (fun e => ~~ (e # (frf e))) dom.

Hypothesis Consistent : dom_consistency.

Lemma rff_consist e : e # (frf e) = false.
Proof.
  apply/negbTE/negP; case: (boolP (e \in dom)) => [D|nD].
  - by move/allP/(_ _ D)/negP: Consistent.
  rewrite frf_dom // => /cfP[e1 [e2 [[]]]]; do 2 move/ca_notdom/(_ nD)/eqP->.
  by rewrite icfxx.
Qed.

Lemma cf_irrelf : irreflexive cf.
Proof.
  move=> m; apply/negbTE/negP; elim/(@wfb_ind disp E): m=> m IHm.
  suff C: ~ m # (fpred m) by rewrite cfE icfxx orbb /= rff_consist /= orbF.
  move=> /cfP[x [y [[]]]]; case: (eqVneq x m)=> [-> _|].
  - by move=> /ca_le L /and6P[_ /eqP<- _ /(le_lt_trans L)]; rewrite ltxx.
  move/ca_step_last=> /[apply] [[z /and3P[/[swap]]]].
  rewrite /ica !inE=> /pred2P[]-> Cx ?.
  - move=> /ca_fpredr Cy /icf_cf/cf_consist2/(_ Cx Cy).
    by rewrite cf_sym rff_consist.
  by move=> Cy /icf_cf/cf_consist2/(_ Cx Cy); exact/IHm.
Qed.

End ExecEventStructure.

Section Consistency.

Context {disp : unit} {E : identType disp}.
Implicit Type es : (@fin_exec_event_struct disp E).

Inductive cexec_event_struct := Consist es of (dom_consistency es).

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
