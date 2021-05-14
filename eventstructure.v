From Coq Require Import Relations Relation_Operators.
From RelationAlgebra Require Import lattice monoid rel kat_tac.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq path.
From mathcomp Require Import eqtype choice order finmap fintype.
From monae Require Import hierarchy monad_model.
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
(* ext f   == if we have some function f : E -> E we can extend it to the     *)
(*            function of type lad_pred_rfrom -> lad_pred_rfrom, applying f   *)
(*            just to the 2nd and 3rd components                              *)
(*                                                                            *)
(* One can prove irreflexivity of the conflict relation under the assumption  *)
(* that reads are not in conflict with the writes they read from:             *)
(*   cexec_event_structure == a subtype of finite execution event structures  *)
(*                            with irreflexive conflict relation              *)
(******************************************************************************)

Import Order.LTheory.
Open Scope order_scope.
Import WfClosure.

Set Implicit Arguments.
Unset Strict Implicit.

Declare Scope exec_eventstruct_scope.
Delimit Scope exec_eventstruct_scope with exec_es.

Local Open Scope exec_eventstruct_scope.


(* TODO: make opaque? *)
Definition Loc := nat.

Inductive Lab {RVal WVal : Type} :=
| Read  of Loc & RVal
| Write of Loc & WVal
| ThreadStart
| ThreadEnd.

Module Label.
Section Label. 

Context {Val : eqType}.

Local Notation Lab := (@Lab Val Val).

Definition loc : Lab -> option Loc := 
  fun lab =>
    match lab with
    | Write x _ => Some x
    | Read  x _ => Some x
    | _         => None
    end.

Definition value : Lab -> option Val := 
  fun lab =>
    match lab with
    | Write _ v => Some v
    | Read  _ v => Some v
    | _         => None
    end.

Definition is_read : pred Lab := 
  fun l => if l is (Read _ _) then true else false.

Definition is_write : pred Lab := 
  fun l => if l is (Write _ _) then true else false.

Definition is_thrdstart : pred Lab := 
  fun l => if l is ThreadStart then true else false.

Definition is_thrdend : pred Lab := 
  fun l => if l is ThreadEnd then true else false.

Definition eq_lab : rel Lab :=
  fun l1 l2 => 
    match l1, l2 with
    | Read  x a, Read  y b     => [&& a == b & x == y]
    | Write x a, Write y b     => [&& a == b & x == y]
    | ThreadEnd, ThreadEnd     => true
    | ThreadStart, ThreadStart => true
    | _, _                     => false
    end.

Lemma eq_labP : Equality.axiom eq_lab.
Proof.
  case=> [v x [] * /=|v x []* /=|[]|[]]; try constructor=>//;
  by apply: (iffP andP)=> [[/eqP->/eqP->]|[->->]].
Qed.

Definition eq_loc : rel Lab := 
  orelpre loc eq_op.

Definition eq_value : rel Lab := 
  orelpre value eq_op.

(* TODO: invent a better name? 
 *   `synch` clashes with `synchronizes-with` relation 
 *    from weak memory theory, which has slightly different meaning. 
 *)
Definition synch (l1 l2 : Lab) :=
  match l1, l2 with
  (* write synchronizes with a read with the matching value *)
  | Write x a, Read y b  => (x == y) && (a == b)
  (* otherwise there is no synchronization *)
  | _, _ => false
  end.

(* Lemma rf_thrdend w : write_read_from w ThreadEnd = false. *)
(* Proof. by case: w. Qed. *)

End Label.

Module Exports.
Section Label.
Context {V : eqType}.
Canonical Lab_eqMixin := EqMixin (@eq_labP V).
Canonical Lab_eqType  := Eval hnf in EqType (@Lab V V) Lab_eqMixin.
End Label.
End Exports. 

Module Syntax. 
Notation "l1 \>> l2" := (Label.synch l1 l2) (no associativity, at level 20).
End Syntax. 

End Label.

Export Label.Exports. 
Import Label.Syntax. 

(* ************************************************************************* *)
(*     Exec Event Structure                                                  *)
(* ************************************************************************* *)

Section ExecEventStructureDef.

Context {disp : unit} (E : identType disp) (Val : eqType).

Local Notation Lab := (@Lab Val Val).

Implicit Type l : Lab.

(* lprf stands for label, predecessor, reads-from *)
Record lab_pred_rfrom := Lprf {lab_prj : Lab; fpred_prj : E; frf_prj : E}.

Definition ext (f : E -> E) (lprf : lab_pred_rfrom) :=
  let: Lprf l p r := lprf in
  Lprf l (f p) (f r).

Lemma ext_id: ext id =1 id.
Proof. by case. Qed.

Lemma ext_comp f g: ext (f \o g) =1 ext f \o ext g.
Proof. by case. Qed.

Lemma ext_can f g: cancel f g -> cancel (ext f) (ext g).
Proof. move=> ? [/= ???]; exact/congr2. Qed.

Lemma bij_ext f: bijective f -> bijective (ext f).
Proof. case=> g *; exists (ext g); exact/ext_can. Qed.

Definition prod_of_lprf lprf :=
  let: Lprf l p rf := lprf in (l, p, rf).

Definition lprf_of_prod p :=
  let: (l, p, rf) := p in Lprf l p rf.

Lemma prod_of_lprfK : cancel prod_of_lprf lprf_of_prod. 
Proof. by case. Qed.

Definition lprf_eqMixin := CanEqMixin prod_of_lprfK.

Canonical lprf_eqType := Eval hnf in EqType lab_pred_rfrom lprf_eqMixin.

Local Open Scope fset_scope.

Structure fin_exec_event_struct := Pack {
  dom        : seq E;
  lprf       : { fsfun for fun e =>
                   {| lab_prj   := ThreadEnd;
                      fpred_prj := e;
                      frf_prj   := e |} };
  dom_sorted : sorted (>%O) dom;
  dom0       : ident0 \in dom;
  _          : finsupp lprf == (seq_fset tt dom `\ ident0);
  lab e      := lab_prj (lprf e);
  fpred e    := fpred_prj (lprf e);
  frf e      := frf_prj (lprf e);
  _          : [forall e : finsupp lprf, fpred (val e) < val e];
  _          : [forall e : finsupp lprf, frf   (val e) < val e];
  _          : [forall rs : seq_fset tt dom, 
                  let r := val rs in
                  let w := frf r  in
                  ((w == ident0) && ~~ Label.is_read (lab r)) || ((lab w) \>> (lab r))];
}.

End ExecEventStructureDef.

Arguments dom_sorted {_ _ _ _}.

Section ExecEventStructEq. 

Context {disp} {E : identType disp} {Val : eqType}.

Definition eq_es (es es' : fin_exec_event_struct E Val) : bool :=
  [&& dom es == dom es' & lprf es == lprf es'].

Lemma eqesP : Equality.axiom eq_es.
Proof.
  move=> x y; apply: (iffP idP)=> [|->]; last by rewrite /eq_es ?eq_refl.
  case: x=> d1 l1 i1 s1 ds1 lab1; rewrite {}/lab1 => pc1 rc1 rc1'.
  case: y=> d2 l2 i2 s2 ds2 lab2; rewrite {}/lab2 => pc2 rc2 rc2'.
  case/andP=> /= /eqP E1 /eqP E2.
  move: E1 E2 ds1 i1 s1 s2 pc1 rc1 rc1' ds2 i2 pc2 rc2 rc2'; (do 2 case: _ /).
  move=> *; congr Pack; exact/eq_irrelevance.
Qed.

End ExecEventStructEq. 

(* ************************************************************************* *)
(*     Label related functions, predicates and relations on events           *)
(* ************************************************************************* *)

Section ExecEventStructLab. 
Context {disp} {E : identType disp} {Val : eqType}.
Context (x : Loc) (v : Val).
Context (es : fin_exec_event_struct E Val).

Notation lab := (lab es).

Definition loc : E -> option Loc := 
  Label.loc \o lab. 

Definition value : E -> option Val := 
  Label.value \o lab. 

Definition with_loc : pred E := 
  opreim loc (eq_op x).

Definition with_value : pred E := 
  opreim value (eq_op v).

Definition is_read : pred E := 
  Label.is_read \o lab. 

Definition is_write : pred E := 
  Label.is_write \o lab. 

Definition is_thrdstart : pred E := 
  Label.is_thrdstart \o lab. 

Definition is_thrdend : pred E := 
  Label.is_thrdend \o lab. 

Definition eq_lab : rel E :=
  relpre lab Label.eq_lab.  

Definition eq_loc : rel E := 
  relpre lab Label.eq_loc.  

Definition eq_value : rel E := 
  relpre lab Label.eq_value.

End ExecEventStructLab. 

(* ************************************************************************* *)
(*     Notations to filter out events of an event structure                  *)
(* ************************************************************************* *)

Notation "[ 'events' 'of' S | P ]" := 
  (filter (P S) (dom S)) 
    (at level 0) : exec_eventstruct_scope. 

Notation "[ 'events' 'of' S | P1 & P2 ]" := 
  (filter (fun e => P1 S e && P2 S e) (dom S)) 
    (at level 0) : exec_eventstruct_scope. 

Notation "[ 'events' e <- S | C ]" := 
  (filter (fun e => C) (dom S)) 
    (at level 0) : exec_eventstruct_scope.

Notation "[ 'events' e <- S | C1 & C2 ]" := 
  (filter (fun e => C1 && C2) (dom S)) 
    (at level 0) : exec_eventstruct_scope.


Section ExecEventStructure.
Context {disp} {E : identType disp} {Val : eqType}.
Context (es : fin_exec_event_struct E Val).

Local Open Scope fset_scope.

Notation lprf := (lprf es).
Notation dom := (dom es).
Notation lab := (lab es).
Notation fpred := (fpred es).
Notation frf := (frf es).

(* ************************************************************************* *)
(*     Auxiliary lemmas about labels                                         *)
(* ************************************************************************* *)

Lemma labE e : lab e = lab_prj (lprf e).
Proof. by []. Qed.

Lemma fpredE e : fpred e = fpred_prj (lprf e).
Proof. by []. Qed.

Lemma frfE e : frf e = frf_prj (lprf e).
Proof. by []. Qed.

Lemma frf_prj_ext e f: 
  frf_prj (ext f (lprf e)) = f (frf e).
Proof. rewrite /frf; by case: (lprf e). Qed.

Lemma fpred_prj_ext e f: 
  fpred_prj (ext f (lprf e)) = f (fpred e).
Proof. rewrite /fpred; by case: (lprf e). Qed.


Lemma lprf_dom : (finsupp lprf) =i [seq x <- dom | x != ident0].
Proof. 
  case: es=> ???? /[dup] /fset_eqP + * x /=.
  by move/(_ x)=>->; rewrite ?inE mem_filter seq_fsetE. 
Qed.

(***** Labels and Freshness *****)
Section LabelsFresh.

Notation fresh_id := (fresh_seq dom).


Lemma lab0 : lab ident0 = ThreadEnd.
Proof. by rewrite /lab fsfun_dflt // lprf_dom mem_filter eq_refl. Qed.

Lemma lab_fresh : lab fresh_id = ThreadEnd.
Proof. 
  rewrite /lab fsfun_dflt // lprf_dom mem_filter negb_and fresh_seq_notin //.
  exact/dom_sorted.
Qed.

Lemma ident0_fresh: ident0 < fresh_id.
Proof. exact/ident0_fresh_seq. Qed.

End LabelsFresh.

(* ************************************************************************* *)
(*     Predecessor                                                           *)
(* ************************************************************************* *)

Lemma fpred_dom e :
  e \notin dom -> fpred e = e.
Proof. 
  move=> ndom.
  by rewrite /fpred fsfun_dflt // lprf_dom mem_filter negb_and ndom.
Qed.

Lemma fpred0: fpred ident0 = ident0.
Proof.
  by rewrite /fpred fsfun_dflt // lprf_dom mem_filter eq_refl.
Qed.

Lemma fpred_dom_lt: {in finsupp lprf, forall e, fpred e < e}.
Proof.
  case: es=> ????; rewrite /eventstructure.fpred /==> ? /forallP + * x I.
  by move/(_ [` I]).
Qed.

Lemma fpred_le e: fpred e <= e.
Proof.
  case: (boolP (e \in finsupp lprf))=> [/fpred_dom_lt/ltW//|?].
  by rewrite /fpred fsfun_dflt .
Qed.

(* ************************************************************************* *)
(*     Reads-From                                                            *)
(* ************************************************************************* *)

Lemma frf_dom e :
e \notin dom -> frf e = e.
Proof. 
  move=> ndom.
  by rewrite /frf fsfun_dflt // lprf_dom mem_filter negb_and ndom.
Qed.

Lemma frf0: frf ident0 = ident0.
Proof.
  by rewrite /frf fsfun_dflt // lprf_dom mem_filter eq_refl.
Qed.

Lemma frf_dom_lt: {in finsupp lprf, forall e, frf e < e}.
Proof.
  case: es=> ?????; rewrite /eventstructure.frf /==> ? /forallP + * x I.
  by move/(_ [` I]).
Qed.

Lemma frf_le e: frf e <= e.
Proof.
  case: (boolP (e \in finsupp lprf))=> [/frf_dom_lt/ltW//|?].
  by rewrite /frf fsfun_dflt .
Qed.

Lemma frf_cond r : r \in dom -> let w := frf r in
  ((w == ident0) && ~~ Label.is_read (lab r)) || ((lab w) \>> (lab r)).
Proof.
  rewrite -(@seq_fsetE tt); case: es=> /= d;
  rewrite /eventstructure.frf /eventstructure.lab /= .
  by move=> ?????? /forallP /[swap] L /(_ [`L]) /=.
Qed.

Definition fica e : ModelNondet.list E := [:: frf e; fpred e].

Lemma fica_dom e :
  e \notin dom -> fica e = [:: e; e].
Proof. by move=> nI; rewrite /fica frf_dom // fpred_dom. Qed.

Lemma fica_finsupp e :
  e \notin finsupp lprf -> fica e = [:: e; e].
Proof. by move=> ?; rewrite /fica /frf /fpred ?fsfun_dflt //. Qed.

Lemma fica_ge : (@sfrel _ monad.id_ndmorph E) fica ≦ (>=%O : rel E).
Proof. 
  move=> ?? /=; red; rewrite /sfrel /=.
  rewrite ?inE=> /orP[]/eqP->; [exact: frf_le | exact: fpred_le]. 
Qed.

(* TODO: consider to generalize this lemma and move to `relations.v` *)
Lemma fica_gt :
  (@sfrel _ monad.id_ndmorph E (strictify E _ fica)) ≦ (>%O : rel E).
Proof. 
  rewrite strictify_weq.
  (* TODO: can ssreflect rewrite do setoid rewrites? *)
  rewrite -> fica_ge.
  move=> x y //=; red.
  by rewrite lt_def andbC eq_sym.
Qed.

(* ************************************************************************* *)
(*     Causality                                                             *)
(* ************************************************************************* *)

(* Immediate causality relation *)
Definition ica : {dhrel E & E} := 
  (@sfrel _ monad.id_ndmorph E fica : {dhrel E & E})°.

Lemma icaE : ica =2 [rel e1 e2 | e1 \in fica e2].
Proof. by []. Qed.

Lemma ica_le e1 e2 : ica e1 e2 -> e1 <= e2.
Proof. exact: fica_ge. Qed.

(* Causality relation *)
Definition ca : rel E := (rt_closure fica_gt)°.

Lemma closureP e1 e2 :
  reflect (clos_refl_trans _ ica e1 e2) (ca e1 e2).
Proof. 
  rewrite /ca /ica. apply weq_reflect.
  rewrite !clos_refl_trans_hrel_str.
  rewrite rel_cnv_m -kleene.cnvstr.
  apply cnv_weq_iff.
  rewrite cnv_invol str_itr itr_qmk.
  rewrite -qmk_sub_one; last first.
  (* TODO: make a lemma? *)
  - rewrite -rel_top_m -rel_one_m -rel_neg_m -rel_cup_m.
    apply /rel_weq_m/dhrel_eq_dec.
  rewrite kleene.itr_weq; last first.
  - rewrite -rel_one_m -rel_sub_m -rel_cup_m.
    by apply /rel_weq_m; rewrite -strictify_weq.
  rewrite rel_qmk_m.
  rewrite -itr_qmk -str_itr.
  rewrite -clos_refl_trans_hrel_str.
  apply /reflect_weq/rt_closureP.
Qed.

Lemma closure_n1P e1 e2 :
  reflect (clos_refl_trans_n1 _ ica e1 e2) (ca e1 e2).
Proof. 
  apply /(equivP (closureP e1 e2)).
  exact: clos_rt_rtn1_iff. 
Qed.

Lemma ica_ca : ica ≦ ca.
Proof. by move=> x y H; apply /closureP /rt_step. Qed.

(* Lemma ica_ca e1 e2 : ica e1 e2 -> ca e1 e2. *)
(* Proof. exact: rt_closure_subrel. Qed. *)

Lemma ica_fpred {e}: ica (fpred e) e.
Proof. by rewrite icaE /= !inE eqxx. Qed.

Lemma ica_notdom e1 e2:
  e2 \notin dom ->
  ica e1 e2 ->
  e1 == e2.
Proof. by move=> ?; rewrite icaE /= fica_dom // !inE orbb. Qed.

Lemma ica_notfinsupp e1 e2:
  e2 \notin finsupp lprf ->
  ica e1 e2 ->
  e1 == e2.
Proof. by move=> ?; rewrite icaE /= fica_finsupp // !inE orbb. Qed.

Lemma ca_refl {e} : ca e e.
Proof. exact: rt_closure_refl. Qed.

Hint Resolve ca_refl : core.

Lemma ca_trans: transitive ca.
Proof. 
  (* TODO: generalize lemma *)
  rewrite /ca /transitive /= /dhrel_cnv. 
  move=> x y z /[swap]. apply rt_closure_trans.
Qed.

Arguments ca_trans {_ _ _}.

Lemma ca_anti: antisymmetric ca.
Proof. 
  (* TODO: generalize lemma *)
  rewrite /ca /antisymmetric /= /dhrel_cnv. 
  move=> x y. rewrite andbC. apply /rt_closure_antisym. 
Qed.

Lemma ca_le e1 e2 : ca e1 e2 -> e1 <= e2.
Proof. 
  rewrite /ca /= /dhrel_cnv. 
  apply /rt_closure_ge.
Qed.

Lemma ca_step_last e1 e3 :
  e1 != e3 ->
  ca e1 e3 ->
  exists e2, [&& ca e1 e2, ica e2 e3 & e2 < e3].
Proof.
  move/[swap]/closure_n1P; elim=> [/eqP//|] e2 {}e3.
  case: (eqVneq e2 e3)=> [-> _ //| neq23 I23 /closure_n1P C12 _ neq13].
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
  move/closure_n1P; elim=> // {}e2 e3 + _ + N3.
  by move=> /(ica_notdom N3) /eqP-> /(_ N3).
Qed.

Lemma ca_notfinsupp e1 e2:
  ca e1 e2 -> e2 \notin finsupp lprf ->
  e1 == e2.
Proof.
  move/closure_n1P; elim=> // {}e2 e3 + _ + N3.
  by move=> /(ica_notfinsupp N3) /eqP-> /(_ N3).
Qed.

Definition seqpred_ca := wsuffix fica_gt.

Lemma seqpred_ca_in e1 e2 : e1 \in seqpred_ca e2 = ca e1 e2.
Proof. by []. Qed.

(***** Causality and Freshness *****)
Section CausalityFresh.

Notation fresh_id := (fresh_seq dom).

Lemma ica_fresh e: ica fresh_id e -> e = fresh_id.
Proof.
  move/[dup]/ica_ca/ca_notdom/[swap]/fica_ge.
  rewrite /ica ?inE.
  case I: (e \in dom); last by move=> ?/(_ erefl)/eqP->.
  by move: (fresh_seq_lt dom_sorted I)=> /= /lt_geF ->. 
Qed.

Lemma ca_fresh e: ca fresh_id e -> e = fresh_id.
Proof. by move/closure_n1P; elim=> // ?? /[swap] ? /[swap]-> /ica_fresh. Qed.

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
      fpred e1 < e1 &
      fpred e2 < e2].

Lemma icfxx x : icf x x = false.
Proof. by apply/and4P; case; rewrite eq_refl. Qed.

Definition icf_irrefl : irreflexive icf := icfxx.

Hint Resolve icfxx : core.

Lemma icf_sym : symmetric icf.
Proof.
  by move=> e1 e2; apply/and4P/and4P; case=>*; split=> //; rewrite 1?eq_sym.
Qed.

(* Conflict relation *)
Definition cf e1 e2 : bool :=
  has id [seq icf x y | x <- seqpred_ca e1, y <- seqpred_ca e2].

Notation "a \# b" := (cf a b) (at level 10).

Lemma cfP {e1 e2} :
  reflect (exists e1' e2', (ca e1' e1 * ca e2' e2 * icf e1' e2')%type) (e1 \# e2).
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
  e1 \# e2 -> ca e1 e3 -> ca e2 e4 -> e3 \# e4.
Proof.
  move=> /cfP[e1' [e2'] [[/ca_trans C1] /ca_trans C2 *]].
  by apply/cfP; exists e1', e2'; rewrite C1 // C2.
Qed.

Lemma cf_consistl e1 e2 e3 :
  ca e1 e3 -> e1 \# e2 -> e2 \# e3.
Proof. by move=> C13 /cf_consist2 /(_ C13); rewrite cf_sym=>->. Qed.

Lemma cf_consistr e1 e2 e3 :
  ca e2 e3 -> e1 \# e2 -> e1 \# e3.
Proof. by rewrite cf_sym; apply: cf_consistl. Qed.

Lemma icf_cf e1 e2: icf e1 e2 -> e1 \# e2.
Proof. by move=> I; apply/cfP; exists e1, e2; rewrite !ca_refl I. Qed.

Notation cf_step e1 e2 :=
  [|| icf e1 e2,
      has (cf e1) (filter (fun x => e2 != x) (fica e2)) |
      has (cf e2) (filter (fun x => e1 != x) (fica e1))].

Lemma cf_step_cf e1 e2: cf_step e1 e2 -> e1 \# e2.
Proof.
  case/or3P=> [/icf_cf //||] /hasP[e]; rewrite mem_filter => /andP[_ /ica_ca].
  - by apply: cf_consistr.
  by move=> /cf_consistr /[apply]; rewrite cf_sym.
Qed.


(* TODO: refactor proof *)
Lemma cfE e1 e2: e1 \# e2 = cf_step e1 e2.
Proof.
  apply/idP/idP; last by apply: cf_step_cf.
  case/cfP=> e1' [e2' [[]]].
  case: (boolP (e1' == e1))=> [/eqP-> _|].
  - case: (boolP (e2' == e2))=> [/eqP->_->|]; first (apply/orP; by left).
    move/ca_step_last/[apply] => [[x /and3P[/cf_consistr H N + /icf_cf/H]]].
    rewrite lt_neqAle=> /andP[] *.
    have-> //: has (cf e1) [seq x0 <- fica e2 | e2 != x0].
    apply/hasP; exists x=> //; rewrite mem_filter; apply/andP; split=> //.
    by rewrite eq_sym.
  move/ca_step_last/[apply] => [[x /and3P[++++ /icf_cf/cf_consist2 H]]].
  rewrite lt_neqAle eq_sym; move/H => C ? /andP[? _] /C ?.
  have-> //: has (cf e2) [seq x0 <- fica e1 | e1 != x0].
  apply/hasP; exists x=> //; rewrite ?mem_filter 1?cf_sym //; exact/andP. 
Qed.

Lemma cfx0 e: ~~ cf e ident0.
Proof.
  apply/negP=> /cfP[?[?[[?/ca_notfinsupp]]]].
  rewrite lprf_dom mem_filter eq_refl=> /(_ erefl)/eqP-> /and4P[]. 
  by rewrite fpred0 ltxx.
Qed.


(* ************************************************************************* *)
(*     Reads-From Consistency                                                *)
(* ************************************************************************* *)

Definition dom_consistency := 
  all (fun e => (frf e != e) ==> ~~ (e \# (frf e))) dom.

Hypothesis Consistent : dom_consistency.

Lemma rff_consist e : (frf e) != e -> e \# (frf e) = false.
Proof.
  move=> N. apply/negbTE/negP; case: (boolP (e \in dom)) => [D|nD].
  - move/allP/(_ _ D)/negP: Consistent; rewrite N; by apply/contra_not=>->.
  rewrite frf_dom // => /cfP[e1 [e2 [[]]]]; do 2 move/ca_notdom/(_ nD)/eqP->.
  by rewrite icfxx.
Qed.

Lemma cf_irrelf : irreflexive cf.
Proof.
  move=> m; apply/negbTE/negP; elim/(@wfb_ind disp E): m=> m IHm.
  suff C: ~ m \# (fpred m).
  case: (boolP (frf m == m))=> [/eqP fE|?].
  - rewrite cfE => /orP; rewrite orbb icfxx => [[]] //=.
  rewrite fE; case: ifP=> [/eqP//|_]; case: ifP=>//= _; by rewrite orbF => /C.
  rewrite cfE icfxx orbb=> /hasP[? /(mem_subseq (filter_subseq _ _))] /=.
  by rewrite ?inE=> /orP[/eqP->|/eqP->/C]//; rewrite rff_consist.
  move=> /cfP[x [y [[]]]]; case: (eqVneq x m)=> [-> _|].
  - by move=> /ca_le L /and4P[_ /eqP<- _ /(le_lt_trans L)]; rewrite ltxx.
  move/ca_step_last=> /[apply] [[z /and3P[/[swap]]]].
  rewrite icaE /= !inE=> /pred2P[]-> Cx L.
  - move=> /ca_fpredr Cy /icf_cf/cf_consist2/(_ Cx Cy).
    rewrite cf_sym rff_consist //=. 
    apply/eqP=> fE; by rewrite fE ltxx in L.
  by move=> Cy /icf_cf/cf_consist2/(_ Cx Cy); exact/IHm.
Qed.

End ExecEventStructure.

Canonical es_eqMixin disp E V := EqMixin (@eqesP disp E V).
Canonical es_eqType disp E V := 
  Eval hnf in EqType (@fin_exec_event_struct disp E V) (es_eqMixin E V).

Section Consistency.

Context {disp : unit} (E : identType disp) (V : eqType).
Implicit Type es : (@fin_exec_event_struct disp E V).

Inductive cexec_event_struct := Consist es of (dom_consistency es).

Arguments Consist {_}.

Coercion ev_struct_of (ces : cexec_event_struct) :=
  let '(Consist es _) := ces in es.

Canonical consist_subType := [subType for ev_struct_of].

Lemma consist_inj : injective (ev_struct_of).
Proof. exact: val_inj. Qed.

End Consistency.

(*Notation "x <c= y" := (@Order.le ev_display _ x y) (at level 10).*)
Notation "e '|-' a # b" := (cf e a b) (at level 10).
