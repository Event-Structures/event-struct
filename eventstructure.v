From Coq Require Import Relations Relation_Operators.
From RelationAlgebra Require Import lattice monoid rel kat_tac.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq path.
From mathcomp Require Import eqtype choice order finmap fintype finfun.
From monae Require Import hierarchy monad_model.
From event_struct Require Import utilities relations wftype ident inhtype.

(******************************************************************************)
(* This file contains the definitions of:                                     *)
(* Event labels:                                                              *)
(*   Lab R W == an event label telling its type: read, write, the start of    *)
(*                of a thread or the end of a thread                          *)
(* l1 \>> l2 == synchronization relation on labels                            *)
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
(*   fpo e == the program order predecessor of the event e,                   *)
(*            fpo is a finitely supported function that shoud return          *) 
(*            e if e is outside of dom.                                       *)
(*   frf e == finite function that by x returns element form that x reads     *)
(*              if lab x = Read and ident0 otherwise                          *)
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

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Set Equations Transparent.

Import Order.LTheory.
Open Scope order_scope.

Import WfClosure.

Declare Scope exec_eventstruct_scope.
Delimit Scope exec_eventstruct_scope with exec_es.

Local Open Scope exec_eventstruct_scope.

(* ************************************************************************* *)
(*     Label                                                                 *)
(* ************************************************************************* *)

(* TODO: make opaque? *)
Definition Loc := nat.

Inductive Lab {RVal WVal : Type} :=
| Read  of Loc & RVal
| Write of Loc & WVal
| ThreadStart
| ThreadEnd
| Init
| Eps.

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

Definition is_init : pred Lab := 
  fun l => if l is Init then true else false.

Definition is_eps : pred Lab := 
  fun l => if l is Eps then true else false.

Definition eq_lab : rel Lab :=
  fun l1 l2 => 
    match l1, l2 with
    | Read  x a  , Read  y b     => [&& a == b & x == y]
    | Write x a  , Write y b     => [&& a == b & x == y]
    | ThreadEnd  , ThreadEnd     => true
    | ThreadStart, ThreadStart   => true
    | Init       , Init          => true
    | Eps        , Eps           => true
    | _, _                       => false
    end.

Lemma eq_labP : Equality.axiom eq_lab.
Proof.
  case=> [v x [] * /=|v x []* /=|[]|[]|[]|[]]; try constructor=>//;
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
  (* non-read events synchronize with initial event *)
  | Init, Read _ _ => false
  | Init, _        => true
  (* epsilon synchronizes with itself *)
  | Eps, Eps => true
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
(*     Event Descriptor                                                      *)
(* ************************************************************************* *)

(* Event descriptor contains label of an event, 
 * its program order and reads-from predecessors 
 *)
Record edescr (E : Type) (L : Type) := mk_edescr {
  lab_prj : L; 
  fpo_prj : E; 
  frf_prj : E;
}.

Section EDescrMap.

Context {L : Type}.

Local Notation edescr E := (edescr E L) (only parsing).

Definition edescr_map {E1 E2 : Type} : (E1 -> E2) -> edescr E1 -> edescr E2 :=
  fun f ed => 
    let: mk_edescr l e_po e_rf := ed in
    mk_edescr l (f e_po) (f e_rf).

(* TODO: prove functor and monad laws? *)

Lemma edescr_map_id {E : Type} : 
  edescr_map id =1 (id : edescr E -> edescr E).
Proof. by case. Qed.

Lemma edescr_map_eqfun {E1 E2 : Type} (f : E1 -> E2) (g : E1 -> E2) : 
  f =1 g -> edescr_map f =1 edescr_map g.
Proof. by move=> H [/=] ???; rewrite ?H. Qed.

Lemma edescr_map_comp {E1 E2 E3 : Type} (f : E2 -> E3) (g : E1 -> E2) : 
  edescr_map (f \o g) =1 edescr_map f \o edescr_map g.
Proof. by case. Qed.

Lemma edescr_map_can {E1 E2 : Type} (f : E1 -> E2) (g : E2 -> E1) : 
  cancel f g -> cancel (edescr_map f) (edescr_map g).
Proof. move=> ? [/= ???]; exact/congr2. Qed.

Lemma edescr_map_bij {E1 E2 : Type} (f : E1 -> E2) : 
  bijective f -> bijective (edescr_map f).
Proof. case=> g *; exists (edescr_map g); exact/edescr_map_can. Qed.

End EDescrMap.

Section EDescrEq. 

Context {E : eqType} {L : eqType}.

Definition prod_of_edescr : edescr E L -> (L * E * E) :=
  fun ed => 
    let: mk_edescr l e_po e_rf := ed in (l, e_po, e_rf).

Definition edescr_of_prod : (L * E * E) -> edescr E L := 
  fun tup => 
    let: (l, e_po, e_rf) := tup in mk_edescr l e_po e_rf.

Lemma prod_of_edescrK : cancel prod_of_edescr edescr_of_prod. 
Proof. by case. Qed.

Definition edescr_eqMixin := CanEqMixin prod_of_edescrK.
Canonical edescr_eqType := Eval hnf in EqType (edescr E L) edescr_eqMixin.

End EDescrEq.

(* ************************************************************************* *)
(*     Exec Event Structure                                                  *)
(* ************************************************************************* *)

Section ExecEventStructureDef.

Context {disp : unit} (E : identType disp) (V : eqType).

Local Notation Lab := (@Lab V V).
Local Notation edescr := (edescr E Lab).

Implicit Type l : Lab.

Lemma edescr_eq (ed1 ed2 : edescr) : 
  ed1 == ed2 = [&& lab_prj ed1 == lab_prj ed2
                 , fpo_prj ed1 == fpo_prj ed2 
                 & frf_prj ed1 == frf_prj ed2].
Proof. 
  case: ed1 ed2=>???[*/=]; rewrite {1}/eq_op /=.
  rewrite -pair_eqE !/pair_eq /= -pair_eqE !/pair_eq /=.
  by rewrite andbA.
Qed.

Local Open Scope fset_scope.

Structure fin_exec_event_struct := Pack {
  dom        : seq E;
  fed        : { fsfun for fun e =>
                   {| lab_prj := Eps;
                      fpo_prj := e;
                      frf_prj := e; 
                   |} : edescr
               };

  lab e      := lab_prj (fed e);
  fpo e      := fpo_prj (fed e);
  frf e      := frf_prj (fed e);

  _          : finsupp fed == (seq_fset tt dom);
  dom_sorted : sorted (>%O) dom;
  dom0       : \i0 \in dom;

  _          : fed \i0 = {| lab_prj := Init   ; 
                            fpo_prj := ident0 ;
                            frf_prj := ident0 ;
                         |};

  _          : [forall e : finsupp fed, fpo (val e) \in dom];
  _          : [forall e : finsupp fed, frf (val e) \in dom];

  _          : [forall e : finsupp fed, fpo (val e) <= val e];
  _          : [forall e : finsupp fed, frf (val e) <= val e];

  _          : [forall e : finsupp fed, lab (frf (val e)) \>> lab (val e)]; 
}.

Open Scope fmap_scope.

Lemma inh_exec_event_structure : fin_exec_event_struct.
Proof.
  pose dom0 := ([:: \i0] : seq E).
  pose fed0 := [fsfun [fsfun] with ident0 |-> mk_edescr Init \i0 \i0] :
    {fsfun for fun e => mk_edescr Eps e e : edescr}.
  have S: finsupp fed0 =i [:: \i0] => [?|].
  - by rewrite /fed0 finsupp_with /= finsupp0 ?inE orbF.
  have F: fed0 \i0 = mk_edescr Init \i0 \i0 by rewrite ?fsfun_with.
  have [: a1 a2 a3 a4 a5 a6 a7 a8 a9] @evstr : 
  fin_exec_event_struct := Pack dom0 fed0 a1 a2 a3 a4 a5 a6 a7 a8 a9;
  rewrite /dom0 ?inE ?eq_refl //.
  - by apply/eqP/fsetP=> ?; rewrite S seq_fsetE.
  all: by apply/forallP=> [[/= x]]; rewrite S ?inE=> /eqP-> /[! F]/=.
Defined.

End ExecEventStructureDef.

Arguments dom_sorted {_ _ _ _}.

Section ExecEventStructEq. 

Context {disp} {E : identType disp} {Val : eqType}.

Definition eq_es (es es' : fin_exec_event_struct E Val) : bool :=
  [&& dom es == dom es' & fed es == fed es'].

Lemma eqesP : Equality.axiom eq_es.
Proof.
  move=> x y; apply: (iffP idP)=> [|->]; last by rewrite /eq_es ?eq_refl.
  case: x=> dom1 fed1 lab1 fpo1 frf1 df1 ds1 di1. 
  rewrite {}/lab1 {}/fpo1 {}/frf1=> li1 pc1 f1 g1 rc1 rc1'.
  case: y=> dom2 fed2 lab2 fpo2 frf2 df2 ds2 di2.
  rewrite {}/lab2 {}/fpo2 {}/frf2=> li2 pc2 f2 g2 rc2 rc2'.
  case/andP=> /= /eqP E1 /eqP E2. 
  move: df1 ds1 di1 li1 pc1 f1 g1 rc1 rc1'. 
  move: df2 ds2 di2 li2 pc2 f2 g2 rc2 rc2'. 
  move: E1 E2; do 2 (case: _ /). 
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

Local Notation Lab := (@Lab Val Val).

Local Notation fed := (fed es).
Local Notation dom := (dom es).
Local Notation lab := (lab es).
Local Notation fpo := (fpo es).
Local Notation frf := (frf es).

(* ************************************************************************* *)
(*     Auxiliary lemmas                                                      *)
(* ************************************************************************* *)

Lemma fed_dom : (finsupp fed) =i dom.
Proof. 
  case: es=> ????? /[dup] /fset_eqP + * x /=.
  by move/(_ x)=>->; rewrite ?inE seq_fsetE. 
Qed.

Lemma fed_dom_mem x: 
  x \in dom = (x \in finsupp fed).
Proof.
  rewrite fed_dom /=.
  case: (boolP (x == \i0))=> // /eqP->; exact/dom0.
Qed.

Lemma fed0 : 
  fed ident0 = {| lab_prj := Init; fpo_prj := ident0; frf_prj := ident0 |}.
Proof. by case es. Qed.

Lemma fed_ndom e: e \notin dom ->
  fed e = mk_edescr Eps e e.
Proof. by rewrite fed_dom_mem=> ?; rewrite fsfun_dflt. Qed.

Lemma labE e : lab e = lab_prj (fed e).
Proof. by []. Qed.

Lemma fpoE e : fpo e = fpo_prj (fed e).
Proof. by []. Qed.

Lemma frfE e : frf e = frf_prj (fed e).
Proof. by []. Qed.

Lemma lab_prj_edescr_map f e : 
  @lab_prj E Lab (edescr_map f (fed e)) = lab e.
Proof. by rewrite /lab; case: (fed e). Qed.

Lemma fpo_prj_edescr_map f e : 
  @fpo_prj E Lab (edescr_map f (fed e)) = f (fpo e).
Proof. by rewrite /fpo; case: (fed e). Qed.

Lemma frf_prj_edescr_map f e : 
  @frf_prj E Lab (edescr_map f (fed e)) = f (frf e).
Proof. by rewrite /frf; case: (fed e). Qed.

Notation fresh_id := (fresh_seq dom).

Lemma lab0 : lab ident0 = Init.
Proof. by rewrite labE; case es=> ???????? H ??? /=; rewrite H. Qed.

Lemma lab_fresh : lab fresh_id = Eps.
Proof. 
  rewrite /lab fsfun_dflt // fed_dom fresh_seq_notin //.
  exact/dom_sorted.
Qed.

Lemma i0_fresh : \i0 < fresh_id.
Proof. exact/i0_fresh_seq. Qed.

(* ************************************************************************* *)
(*     Program Order                                                         *)
(* ************************************************************************* *)

Lemma fpo0 : fpo \i0 = \i0.
Proof. by rewrite /fpo fed0. Qed.

Lemma fpo_dom e: 
  e \in dom -> fpo e \in dom.
Proof.
  rewrite fed_dom_mem.
  case: es=> /=; rewrite /eventstructure.fpo /==>> ???? /forallP H ???? L.
  exact/(H [` L]).
Qed.

Lemma fpo_ndom e : e \notin dom -> fpo e = e.
Proof. by move=> ndom; rewrite /fpo fsfun_dflt // fed_dom ndom. Qed.

Lemma fpo_le e : fpo e <= e.
Proof.
  rewrite /fpo; case (boolP (e \in finsupp fed)).
  - case: es=> ??????????? H ?? /= eI. 
    rewrite -[e]/(fsval [` eI]).
    move: H=> /forallP H; exact: H.
  by move=> ndom; rewrite fsfun_dflt.  
Qed.

Lemma fpo_fresh e: 
  fpo e = fresh_id -> e = fresh_id.
Proof.
  case: (boolP (e \in dom))=> [/(fresh_seq_lt dom_sorted)|/fpo_ndom->//].
  by move/le_lt_trans: (fpo_le e)=> /[apply]/[swap]-> /[! (@ltxx disp)].
Qed.

(* ************************************************************************* *)
(*     Reads-From                                                            *)
(* ************************************************************************* *)

Lemma frf0 : frf \i0 = \i0.
Proof. by rewrite /frf fed0. Qed.

Lemma frf_dom e: 
  e \in dom -> frf e \in dom.
Proof.
  rewrite fed_dom_mem.
  case: es=> /=; rewrite /eventstructure.frf /==>> ????? /forallP H ??? L.
  exact/(H [` L]).
Qed.

Lemma frf_ndom e : e \notin dom -> frf e = e.
Proof. by move=> ndom; rewrite /frf fsfun_dflt // fed_dom ndom. Qed.

Lemma frf_le e : frf e <= e.
Proof.
  rewrite /frf; case (boolP (e \in finsupp fed)).
  - case: es=> ???????????? H ? /= eI. 
    rewrite -[e]/(fsval [` eI]).
    move: H=> /forallP H; exact: H.
  by move=> ndom; rewrite fsfun_dflt.  
Qed.

Lemma frf_sync e : lab (frf e) \>> lab e. 
Proof.
  rewrite /lab /fed /frf; case (boolP (e \in finsupp fed)).
  - case: es=> ????????????? H /= eI. 
    rewrite -[e]/(fsval [` eI]).
    move: H=> /forallP H; exact: H.
  by move=> ndom; rewrite !fsfun_dflt.
Qed.

Lemma frf_fresh e: 
  frf e = fresh_id -> e = fresh_id.
Proof.
  case: (boolP (e \in dom))=> [/(fresh_seq_lt dom_sorted)|/frf_ndom->//].
  by move/le_lt_trans: (frf_le e)=> /[apply]/[swap]-> /[! (@ltxx disp)].
Qed.

(* ************************************************************************* *)
(*     Causality                                                             *)
(* ************************************************************************* *)

Definition fica e : ModelNondet.list E := [:: frf e; fpo e].

Lemma fica_ndom e :
  e \notin dom -> fica e = [:: e; e].
Proof. by move=> nI; rewrite /fica frf_ndom // fpo_ndom. Qed.

Lemma fica_ge : (@sfrel _ monad.id_ndmorph E) fica ≦ (>=%O : rel E).
Proof. 
  move=> ?? /=; red; rewrite /sfrel /=.
  rewrite ?inE=> /orP[]/eqP->; [exact: frf_le | exact: fpo_le]. 
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

Lemma ica_fpo {e} : ica (fpo e) e.
Proof. by rewrite icaE /= !inE eqxx. Qed.

Lemma ica_ndom e1 e2 :
  e2 \notin dom ->
  ica e1 e2 ->
  e1 == e2.
Proof. by move=> ?; rewrite icaE /= fica_ndom // !inE orbb. Qed.

Lemma ica0 e1 :
  ica e1 ident0 -> e1 == ident0.
Proof. by rewrite icaE /fica /= fpo0 frf0 !inE orbb. Qed.

Lemma ca_refl {e} : ca e e.
Proof. exact: rt_closure_refl. Qed.

Hint Resolve ca_refl : core.

Lemma ca_trans : transitive ca.
Proof. 
  (* TODO: generalize lemma *)
  rewrite /ca /transitive /= /dhrel_cnv. 
  move=> x y z /[swap]. apply rt_closure_trans.
Qed.

Arguments ca_trans {_ _ _}.

Lemma ca_anti : antisymmetric ca.
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

Lemma ca_fpo_l {e} : ca (fpo e) e.
Proof. exact/ica_ca/ica_fpo. Qed.

Lemma ca_fpo_r e1 e2 : ca e1 (fpo e2) -> ca e1 e2.
Proof. by move/ca_trans/(_ ca_fpo_l). Qed.

Lemma ca_ndom e1 e2 :
  ca e1 e2 -> e2 \notin dom ->
  e1 == e2.
Proof.
  move/closure_n1P; elim=> // {}e2 e3 + _ + N3.
  by move=> /(ica_ndom e2 e3 N3) /eqP-> /(_ N3).
Qed.

Lemma ca0 e1 :
  ca e1 ident0 -> e1 == ident0.
Proof.
  (* TODO: refactor *)
  suff H: forall e1 e2, e2 == ident0 -> ca e1 e2 -> e1 == ident0.
  - by move=> ?; apply /H.
  move=> {}e1 {}e2 /[swap].
  move/closure_n1P. 
  elim=> // {}e2 e3 /[swap] _ /[swap] H.
  move=> /[swap] /eqP -> ?.
  by apply/H/ica0.
Qed.

Definition seqpred_ca := wsuffix fica_gt.

Lemma seqpred_ca_in e1 e2 : e1 \in seqpred_ca e2 = ca e1 e2.
Proof. by []. Qed.

(***** Causality and Freshness *****)
Section CausalityFresh.

Notation fresh_id := (fresh_seq dom).

Lemma ica_fresh e : ica fresh_id e -> e = fresh_id.
Proof.
  move/[dup]/ica_ca/ca_ndom/[swap]/fica_ge.
  rewrite /ica ?inE.
  case I: (e \in dom); last by move=> ?/(_ erefl)/eqP->.
  by move: (fresh_seq_lt dom_sorted I)=> /= /lt_geF ->. 
Qed.

Lemma ca_fresh e : ca fresh_id e -> e = fresh_id.
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
      fpo e1 == fpo e2,
      fpo e1 < e1 &
      fpo e2 < e2].

Lemma icfxx x : icf x x = false.
Proof. by apply/and4P; case; rewrite eq_refl. Qed.

Definition icf_irrefl : irreflexive icf := icfxx.

Hint Resolve icfxx : core.

Lemma icf_sym : symmetric icf.
Proof.
  by move=> e1 e2; apply/and4P/and4P; case=>*; split=> //; rewrite 1?eq_sym.
Qed.

Lemma icf0 e : ~~ icf e \i0.
Proof. rewrite /icf fpo0 ltxx !andbF //=. Qed.

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

Lemma cf_sym : symmetric cf.
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

Lemma icf_cf e1 e2 : icf e1 e2 -> e1 \# e2.
Proof. by move=> I; apply/cfP; exists e1, e2; rewrite !ca_refl I. Qed.

Notation cf_step e1 e2 :=
  [|| icf e1 e2,
      has (cf e1) (filter (fun x => e2 != x) (fica e2)) |
      has (cf e2) (filter (fun x => e1 != x) (fica e1))].

Lemma cf_step_cf e1 e2 : cf_step e1 e2 -> e1 \# e2.
Proof.
  case/or3P=> [/icf_cf //||] /hasP[e]; rewrite mem_filter => /andP[_ /ica_ca].
  - by apply: cf_consistr.
  by move=> /cf_consistr /[apply]; rewrite cf_sym.
Qed.


(* TODO: refactor proof *)
Lemma cfE e1 e2 : e1 \# e2 = cf_step e1 e2.
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

Lemma cf0 e : ~~ cf e \i0.
Proof.
  apply/negP. move=> /cfP [e1 [e2 [[]]]].
  move=> /[swap] /ca0 /eqP -> ?. 
  by move /(elimN idP)=> H; apply /H/icf0. 
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
  rewrite frf_ndom // => /cfP[e1 [e2 [[]]]]; do 2 move/ca_ndom/(_ nD)/eqP->.
  by rewrite icfxx.
Qed.

Lemma cf_irrelf : irreflexive cf.
Proof.
  move=> m; apply/negbTE/negP; elim/(@wfb_ind disp E): m=> m IHm.
  suff C: ~ m \# (fpo m).
  case: (boolP (frf m == m))=> [/eqP fE|?].
  - rewrite cfE => /orP; rewrite orbb icfxx => [[]] //=.
  rewrite fE; case: ifP=> [/eqP//|_]; case: ifP=>//= _; by rewrite orbF => /C.
  rewrite cfE icfxx orbb=> /hasP[? /(mem_subseq (filter_subseq _ _))] /=.
  by rewrite ?inE=> /orP[/eqP->|/eqP->/C]//; rewrite rff_consist.
  move=> /cfP[x [y [[]]]]; case: (eqVneq x m)=> [-> _|].
  - by move=> /ca_le L /and4P[_ /eqP<- _ /(le_lt_trans L)]; rewrite ltxx.
  move/ca_step_last=> /[apply] [[z /and3P[/[swap]]]].
  rewrite icaE /= !inE=> /pred2P[]-> Cx L.
  - move=> /ca_fpo_r Cy /icf_cf/cf_consist2/(_ Cx Cy).
    rewrite cf_sym rff_consist //=. 
    apply/eqP=> fE; by rewrite fE ltxx in L.
  by move=> Cy /icf_cf/cf_consist2/(_ Cx Cy); exact/IHm.
Qed.

End ExecEventStructure.

Canonical es_eqMixin disp E V := EqMixin (@eqesP disp E V).
Canonical es_eqType disp E V := 
  Eval hnf in EqType (@fin_exec_event_struct disp E V) (es_eqMixin E V).

Definition es_inhMixin {disp E V} := 
  @Inhabitant.Mixin (@fin_exec_event_struct disp E V) _ 
    (inh_exec_event_structure _ _).
Canonical es_inhType disp E V := 
  Eval hnf in Inhabitant (@fin_exec_event_struct disp E V) es_inhMixin.

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
