From Coq Require Import Relations Relation_Operators.
From RelationAlgebra Require Import lattice monoid rel kat_tac.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq path.
From mathcomp Require Import eqtype choice order finmap fintype finfun.
From eventstruct Require Import utils relalg rel order wftype ident inhtype.
From eventstruct Require Import lposet prime_eventstruct.

(******************************************************************************)
(* This file contains the definitions of:                                     *)
(* Event labels:                                                              *)
(*   Lab R W == an event label telling its type: read, write, the start of    *)
(*                of a thread or the end of a thread                          *)
(* l1 \>> l2 == synchronization relation on labels                            *)
(*                                                                            *)
(* Finite execution event structures:                                         *)
(*   porf_eventstruct d E == definition of a event structure built of         *)
(*                           program-order and reads-from relations,          *)
(*                           where E : identType d                            *)
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
(*      cf == conflicting relation.                                           *)
(*                                                                            *)
(* One can prove irreflexivity of the conflict relation under the assumption  *)
(* that reads are not in conflict with the writes they read from:             *)
(*   prime_porf_eventstruct == a subtype of porf event structures             *)
(*                             with irreflexive conflict relation,            *)
(*                             i.e. those that form prime event structure.    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Set Equations Transparent.

Import Order.LTheory.
Import WfClosure.

Local Open Scope order_scope.
Local Open Scope fset_scope.
Local Open Scope fmap_scope.
Local Open Scope ident_scope.

Declare Scope exec_eventstruct_scope.
Delimit Scope exec_eventstruct_scope with exec_es.

Local Open Scope exec_eventstruct_scope.

Definition Addr := nat.

(* ************************************************************************* *)
(*     Label                                                                 *)
(* ************************************************************************* *)

Module Lab.

Section ClassDef.

Record mixin_of (T0 : Type) (b : Equality.class_of T0)
  (T := Equality.Pack b) := Mixin {
  po_synch : rel T;
  rf_synch : rel T;
  init     : T;
  eps      : T;

  _ : init != eps;
  _ : po_synch init init;
  _ : rf_synch init init;
  _ : po_synch eps  eps;
  _ : rf_synch eps  eps;
}.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base   : Equality.class_of T;
  mixin  : mixin_of base;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Equality.class_of.

Structure type := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack :=
  fun b bT & phant_id (Equality.class bT) b => fun m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
End ClassDef.

Module Exports.

Notation labType := type.
Coercion base : class_of >-> Equality.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Notation LabType T m := (@pack T _ _ id m).
Definition init {T : labType} : T := init (mixin (class T)).
Definition eps {T : labType} : T := eps (mixin (class T)).
Definition po_synch {T : labType} : rel T := po_synch (mixin (class T)).
Definition rf_synch {T : labType} : rel T := rf_synch (mixin (class T)).
Notation "[ 'labType' 'of' T 'for' cT ]" := (@clone T cT _ id)
  (at level 0, format "[ 'labType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'labType' 'of' T ]" := [identType of T for _]
  (at level 0, format "[ 'labType'  'of'  T ]") : form_scope.

End Exports.

End Lab.

Export Lab.Exports.

Notation "'\init'" := (@init _).
Notation "'\eps'" := (@eps _).
Notation "l1 '(po)>>' l2" := (po_synch l1 l2) (at level 90).
Notation "l1 '(rf)>>' l2" := (rf_synch l1 l2) (at level 90).


Section LabelTheory.
Context {T : labType}.

Lemma init_eps : \init != \eps :> T.
Proof. by case: T=> ? [? []]. Qed.

Lemma synch :
  (((po_synch (\init : T) \init) *
    (rf_synch (\init : T) \init)) *
   ((rf_synch (\eps  : T) \eps) *
    (po_synch (\eps  : T) \eps)))%type .
Proof. by case: T=> ? [? []]. Qed.

End LabelTheory.

(* TODO: make opaque? *)
Definition Loc := nat.

Inductive Lab {RVal WVal : Type} :=
| Read        of Loc & RVal
| Write       of Loc & WVal
| ThreadFork  of nat & Addr
| ThreadJoin  of nat
| ThreadStart of nat & Addr
| ThreadEnd   of nat
| Init
| Idle
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
  fun l => if l is ThreadStart _ _ then true else false.

Definition is_thrdend : pred Lab := 
  fun l => if l is ThreadEnd _ then true else false.

Definition is_init : pred Lab := 
  fun l => if l is Init then true else false.

Definition is_eps : pred Lab := 
  fun l => if l is Eps then true else false.

Definition eq_lab : rel Lab :=
  fun l1 l2 => 
    match l1, l2 with
    | Read        x a, Read        y b => [&& a == b & x == y]
    | Write       x a, Write       y b => [&& a == b & x == y]
    | ThreadFork  i n, ThreadFork  j m => [&& i == j & n == m]
    | ThreadJoin  i  , ThreadJoin  j   => i == j
    | ThreadStart i n, ThreadStart j m => [&& i == j & n == m]
    | ThreadEnd   i  , ThreadEnd   j   => i == j
    | Init       , Init          => true
    | Eps        , Eps           => true
    | Idle       , Idle          => true
    | _, _                       => false
    end.

Lemma eq_labP : Equality.axiom eq_lab.
Proof.
  case=> [??[]*|??[]*|??[]*|?[]*|??[]*|?[]*|[]|[]|[]] /=; try constructor=>//;
  try by apply: (iffP andP)=> [[/eqP->/eqP->]|[->->]].
  all: by apply: (iffP idP)=> [/eqP->|[->]].
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
  (* thread start synchronizes with a thread fork with the matching value *)
  | ThreadFork i n, ThreadStart j m => (i == j) && (n == m)
  (* thread join synchronizes with a thread end with the matching value *)
  | ThreadEnd i, ThreadJoin j => i == j
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

Lemma edescr_eq (ed1 ed2 : edescr E L) : 
  ed1 == ed2 = [&& lab_prj ed1 == lab_prj ed2
                 , fpo_prj ed1 == fpo_prj ed2 
                 & frf_prj ed1 == frf_prj ed2].
Proof. 
  case: ed1 ed2=>???[*/=]; rewrite {1}/eq_op /=.
  rewrite -pair_eqE !/pair_eq /= -pair_eqE !/pair_eq /=.
  by rewrite andbA.
Qed.

End EDescrEq.

(* ************************************************************************* *)
(*     Exec Event Structure                                                  *)
(* ************************************************************************* *)

Section PORFEventStructureDef.

Context (E : identType) (L : labType).

Local Notation edescr := (edescr E L).

Structure porf_eventstruct := Pack {
  dom    : seq E;
  fed    : { fsfun for fun e =>
               {| lab_prj := \eps;
                  fpo_prj := e;
                  frf_prj := e; 
               |} : edescr
           };

  lab e  := lab_prj (fed e);
  fpo e  := fpo_prj (fed e);
  frf e  := frf_prj (fed e);

  _      : finsupp fed == (seq_fset tt dom);
  _      : \i0 \in dom;

  _      : fed \i0 = {| lab_prj := \init; 
                        fpo_prj := \i0;
                        frf_prj := \i0;
                     |};

  _      : [forall e : finsupp fed, fpo (val e) \in dom];
  _      : [forall e : finsupp fed, frf (val e) \in dom];

  _      : [forall e : finsupp fed, (val e != \i0) ==> (fpo (val e) <^i val e)];
  _      : [forall e : finsupp fed, (val e != \i0) ==> (frf (val e) <^i val e)];

  _      : [forall e : finsupp fed, lab (fpo (val e)) (po)>> lab (val e)]; 
  _      : [forall e : finsupp fed, lab (frf (val e)) (rf)>> lab (val e)]; 
}.

(*
  (st1, l, st2) (po)>> (st1', l', st2')
  1) st2 == st1'
*)

End PORFEventStructureDef.

(* ************************************************************************* *)
(*     Canonical instances for event structure                               *)
(* ************************************************************************* *)

Section PORFEventStructEq. 

Context {E : identType} {L : labType}.

Definition eq_es (es es' : porf_eventstruct E L) : bool :=
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

End PORFEventStructEq. 

Canonical es_eqMixin E L := EqMixin (@eqesP E L).
Canonical es_eqType E L := 
  Eval hnf in EqType (@porf_eventstruct E L) (es_eqMixin E L).

Section PORFEventStructInh. 

Context {E : identType} {L : labType}.

Local Notation edescr := (edescr E L).

Lemma inh_exec_eventstructure : porf_eventstruct E L.
Proof.
  pose dom0 := ([:: \i0] : seq E).
  pose fed0 := [fsfun [fsfun] with ident0 |-> mk_edescr \init \i0 \i0] :
    {fsfun for fun e => mk_edescr \eps e e : edescr}.
  have S: finsupp fed0 =i [:: \i0] => [? |].
  - rewrite /fed0 finsupp_with /= /eq_op /= /eq_op /= /eq_op /=.
    by rewrite (negbTE init_eps) finsupp0 ?inE orbF.
  have F: fed0 \i0 = mk_edescr \init \i0 \i0 by rewrite ?fsfun_with.
  have [: a1 a2 a3 a4 a5 a6 a7 a8 a9] @evstr : 
  porf_eventstruct E L := Pack dom0 fed0 a1 a2 a3 a4 a5 a6 a7 a8 a9;
  rewrite /dom0 ?inE ?eq_refl //.
  - by apply/eqP/fsetP=> ?; rewrite S seq_fsetE.
  all: apply/forallP=> [[/= x]]; rewrite S ?inE=> /eqP-> /[! F]/= //.
  all: by rewrite ?eq_refl ?synch.
Defined.

End PORFEventStructInh. 

Canonical es_inhMixin {E V} := 
  @Inhabitant.Mixin (@porf_eventstruct E V) _ 
    inh_exec_eventstructure.
Canonical es_inhType E V := 
  Eval hnf in Inhabitant (@porf_eventstruct E V) es_inhMixin.

(* ************************************************************************* *)
(*     Label related functions, predicates and relations on events           *)
(* ************************************************************************* *)

Section PORFEventStructLab. 

Context {E : identType} {L : labType}.
Context (x : Loc) (v : L).
Context (es : porf_eventstruct E L).

(*Definition loc : E -> option Loc := 
  Label.loc \o lab es. 

Definition value : E -> option Val := 
  Label.value \o lab es. 

Definition with_loc : pred E := 
  opreim loc (eq_op x).

Definition with_value : pred E := 
  opreim value (eq_op v).

Definition is_read : pred E := 
  Label.is_read \o lab es. 

Definition is_write : pred E := 
  Label.is_write \o lab es. 

Definition is_thrdstart : pred E := 
  Label.is_thrdstart \o lab es. 

Definition is_thrdend : pred E := 
  Label.is_thrdend \o lab es. 

Definition eq_lab : rel E :=
  relpre (lab es) Label.eq_lab.  

Definition eq_loc : rel E := 
  relpre (lab es) Label.eq_loc.  

Definition eq_value : rel E := 
  relpre (lab es) Label.eq_value.*)

End PORFEventStructLab. 

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


Section PORFEventStructureTheory.

Context {E : identType} {L : labType}.
Context (es : porf_eventstruct E L).

Local Notation fed := (fed es).
Local Notation dom := (dom es).
Local Notation lab := (lab es).
Local Notation fpo := (fpo es).
Local Notation frf := (frf es).

Notation fresh_id := (fresh_seq dom).

(* ************************************************************************* *)
(*     Domain and event descriptor mapping                                   *)
(* ************************************************************************* *)

Lemma fed_supp : (finsupp fed) =i dom.
Proof. 
  case: es=> ????? /[dup] /fset_eqP + * x /=.
  by move/(_ x)=>->; rewrite ?inE seq_fsetE. 
Qed.

(* TODO: rewrite with `fed_supp` under `\in`? *)
Lemma fed_supp_mem x: 
  (x \in finsupp fed) = (x \in dom).
Proof.
  rewrite fed_supp /=.
  case: (boolP (x == \i0))=> // /eqP->; exact/dom0.
Qed.

Lemma fed0 : 
  fed ident0 = {| lab_prj := \init; fpo_prj := ident0; frf_prj := ident0 |}.
Proof. by case es. Qed.

Lemma fed_ndom e: e \notin dom ->
  fed e = mk_edescr \eps e e.
Proof. by rewrite -fed_supp_mem=> ?; rewrite fsfun_dflt. Qed.

Lemma dom0 : \i0 \in dom. 
Proof. by case: es. Qed.

(* Lemma dom_sorted : sorted (>%O) dom.  *)
(* Proof. by case: es. Qed. *)

(* ************************************************************************* *)
(*     Label mapping                                                         *)
(* ************************************************************************* *)

Lemma labE e : lab e = lab_prj (fed e).
Proof. by []. Qed.

Lemma lab0 : lab ident0 = \init.
Proof. by rewrite labE fed0. Qed.

Lemma lab_ndom e : e \notin dom -> lab e = \eps.
Proof. by move=> ?; rewrite labE fed_ndom. Qed.

Lemma lab_fresh : lab fresh_id = \eps.
Proof. by rewrite lab_ndom //; apply /fresh_seq_nmem. Qed.

Lemma lab_prj_edescr_map f e : 
  @lab_prj E L (edescr_map f (fed e)) = lab e.
Proof. by rewrite /lab; case: (fed e). Qed.

(* ************************************************************************* *)
(*     Program Order                                                         *)
(* ************************************************************************* *)

Lemma fpoE e : fpo e = fpo_prj (fed e).
Proof. by []. Qed.

Lemma fpo0 : fpo \i0 = \i0.
Proof. by rewrite /fpo fed0. Qed.

Lemma fpo_dom e : 
  e \in dom -> fpo e \in dom.
Proof.
  rewrite -fed_supp_mem.
  case: es=> /=; rewrite /porf_eventstruct.fpo /==>> ??? /forallP H ????? L'.
  exact/(H [` L']).
Qed.

Lemma fpo_ndom e : e \notin dom -> fpo e = e.
Proof. by move=> ndom; rewrite /fpo fsfun_dflt // fed_supp ndom. Qed.

Lemma fpo_n0 e : e \in dom -> e != \i0 -> fpo e <^i e.
Proof.
  rewrite /fpo -fed_supp.
  case: es=> /= > ????? /forallP H ??? eI.
  by move/(_ [` eI])/implyP: H=> /= /[apply].
Qed.

Lemma fpo_le e : fpo e <=^i e.
Proof.
  case: (boolP (e \in dom))=> [/fpo_n0|/fpo_ndom-> //].
  by case: (e =P \i0)=> [->|_ /(_ erefl)/ltW //]; rewrite fpo0.
Qed.

Lemma fpo_fresh e : 
  fpo e = fresh_id -> e = fresh_id.
Proof.
  case: (boolP (e \in dom))=> [/fresh_seq_mem|/fpo_ndom->//].
  by move/le_lt_trans: (fpo_le e)=> /[apply]/[swap]-> /[! (@ltxx)].
Qed.

Lemma fpo_sync e : lab (fpo e) (po)>> lab e. 
Proof.
  rewrite /lab /fed /fpo; case (boolP (e \in finsupp fed)).
  - case: es=> ???????????? H ? /= eI. 
    rewrite -[e]/(fsval [` eI]).
    move: H=> /forallP H; exact: H.
  by move=> ndom; rewrite !fsfun_dflt //= synch.
Qed.

Lemma fpo_prj_edescr_map f e : 
  @fpo_prj E L (edescr_map f (fed e)) = f (fpo e).
Proof. by rewrite /fpo; case: (fed e). Qed.

(* ************************************************************************* *)
(*     Reads-From                                                            *)
(* ************************************************************************* *)

Lemma frfE e : frf e = frf_prj (fed e).
Proof. by []. Qed.

Lemma frf0 : frf \i0 = \i0.
Proof. by rewrite /frf fed0. Qed.

Lemma frf_dom e : 
  e \in dom -> frf e \in dom.
Proof.
  rewrite -fed_supp_mem.
  case: es=> /=; rewrite /porf_eventstruct.frf /==>> ???? /forallP H ???? L'.
  exact/(H [` L']).
Qed.

Lemma frf_ndom e : e \notin dom -> frf e = e.
Proof. by move=> ndom; rewrite /frf fsfun_dflt // fed_supp ndom. Qed.

Lemma frf_n0 e : e \in dom -> e != \i0 -> frf e <^i e.
Proof.
  rewrite /frf -fed_supp.
  case: es=> /= > ?????? /forallP H ?? eI.
  by move/(_ [` eI])/implyP: H=> /= /[apply].
Qed.

Lemma frf_le e : frf e <=^i e.
Proof.
  case: (boolP (e \in dom))=> [/frf_n0|/frf_ndom-> //].
  by case: (e =P \i0)=> [->|_ /(_ erefl)/ltW //]; rewrite frf0.
Qed.

Lemma frf_fresh e : 
  frf e = fresh_id -> e = fresh_id.
Proof.
  case: (boolP (e \in dom))=> [/fresh_seq_mem|/frf_ndom->//].
  by move/le_lt_trans: (frf_le e)=> /[apply]/[swap]-> /[! @ltxx].
Qed.

Lemma frf_sync e : lab (frf e) (rf)>> lab e. 
Proof.
  rewrite /lab /fed /frf; case (boolP (e \in finsupp fed)).
  - case: es=> ????????????? H /= eI. 
    rewrite -[e]/(fsval [` eI]).
    move: H=> /forallP H; exact: H.
  by move=> ndom; rewrite !fsfun_dflt //= synch.
Qed.

Lemma frf_prj_edescr_map f e : 
  @frf_prj E L (edescr_map f (fed e)) = f (frf e).
Proof. by rewrite /frf; case: (fed e). Qed.

(* ************************************************************************* *)
(*     Immediate Causality                                                   *)
(* ************************************************************************* *)

Definition fca e : seq E := [:: fpo e; frf e].

(* TODO: `sfrel` - infer [canonical] instance automatically, 
 *   then get rid of `ica` and use `sfrel fca` inplace
 *)
Definition ica : {dhrel E & E} := 
  (sfrel fca)°.

Lemma fca0 : fca \i0 = [:: \i0 ; \i0].
Proof. by rewrite /fca fpo0 frf0. Qed.

Lemma fca_dom e e' : 
  e \in dom -> e' \in fca e -> e' \in dom.
Proof.
  rewrite /fca !inE.
  move=> ? /orP[/eqP->|/eqP->]; 
    [exact/fpo_dom | exact/frf_dom].
Qed.

Lemma fca_ndom e : e \notin dom -> fca e = [:: e; e].
Proof. by move=> ndom; rewrite /fca (fpo_ndom e ndom) (frf_ndom e ndom). Qed.

Lemma fca_ge : sfrel fca ≦ (>=%O : rel E).
Proof. 
  move=> ?? /=; red; rewrite /sfrel /=.
  rewrite ?inE=> /orP[]/eqP->; [exact: fpo_le | exact: frf_le]. 
Qed.

(* TODO: consider to generalize this lemma and move to `relations.v` *)
Lemma fca_gt :
  (sfrel (strictify fca)) ≦ (>%O : rel E).
Proof. 
  rewrite strictify_weq.
  (* TODO: can ssreflect rewrite do setoid rewrites? *)
  rewrite -> fca_ge.
  move=> x y //=; red.
  by rewrite lt_def andbC eq_sym.
Qed.


Lemma icaE : ica =2 [rel e1 e2 | e1 \in fca e2].
Proof. by []. Qed.

Lemma ica0 e1 :
  ica e1 ident0 -> e1 == ident0.
Proof. by rewrite icaE /= fca0 !inE orbb. Qed.

Lemma ica_fpo e : ica (fpo e) e.
Proof. by rewrite icaE /= !inE eqxx. Qed.

Lemma ica_frf e : ica (frf e) e.
Proof. by rewrite icaE /= !inE eqxx. Qed.

Lemma ica_ndom e1 e2 :
  ica e1 e2 -> e2 \notin dom -> e1 == e2.
Proof. by move=> /[swap] ?; rewrite icaE /= fca_ndom // !inE orbb. Qed.

Lemma ica_le e1 e2 : ica e1 e2 -> e1 <=^i e2.
Proof. exact: fca_ge. Qed.

Lemma ica_fresh e : ica fresh_id e -> e = fresh_id.
Proof.
  move/[dup]/ica_ndom/[swap]/fca_ge.
  rewrite /ica ?inE.
  case I: (e \in dom); last by move=> ?/(_ erefl)/eqP->.
  by move: (fresh_seq_mem I)=> /= /lt_geF ->. 
Qed.

(* ************************************************************************* *)
(*     Causality                                                             *)
(* ************************************************************************* *)

Definition ca : rel E := (rt_closure fca_gt)°.

Lemma closureP e1 e2 :
  reflect (clos_refl_trans ica e1 e2) (ca e1 e2).
Proof. 
  rewrite /ca /ica. apply weq_reflect.
  rewrite !clos_rt_str.
  rewrite rel_cnv_m -kleene.cnvstr.
  apply cnv_weq_iff.
  rewrite cnv_invol str_itr itr_qmk.
  rewrite -(kleene.itr_weq (qmk_sub_one _ _)); last first.
  - rewrite -rel_top_m -rel_one_m -rel_neg_m -rel_cup_m.
    apply /rel_weq_m/dhrel_eq_dec.
  rewrite kleene.itr_weq; last first.
  - rewrite -rel_one_m -rel_sub_m -rel_cup_m.
    by apply /rel_weq_m; rewrite -strictify_weq.
  rewrite (kleene.itr_weq (rel_qmk_m _)).
  rewrite -itr_qmk -str_itr.
  rewrite -clos_rt_str.
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

Lemma ca_fpo e : ca (fpo e) e.
Proof. exact/ica_ca/ica_fpo. Qed.

Lemma ca_frf e : ca (frf e) e.
Proof. exact/ica_ca/ica_frf. Qed.

Lemma ca_ndom e1 e2 :
  ca e1 e2 -> e2 \notin dom -> e1 == e2.
Proof.
  move/closure_n1P; elim=> // {}e2 e3 + _. 
  move=> /[swap] + /(ica_ndom e2 e3)=> H1 H2 /[dup].
  by move/H2=> /eqP<- /H1.
Qed.

Lemma ca_le e1 e2 : ca e1 e2 -> e1 <=^i e2.
Proof. 
  rewrite /ca /= /dhrel_cnv. 
  apply /rt_closure_ge.
Qed.

Lemma ca_refl {e} : ca e e.
Proof. exact: rt_closure_refl. Qed.

Hint Resolve ca_refl : core.

Lemma ca_anti : antisymmetric ca.
Proof. 
  (* TODO: generalize lemma *)
  rewrite /ca /antisymmetric /= /dhrel_cnv. 
  move=> x y. rewrite andbC. apply /rt_closure_antisym. 
Qed.

Lemma ca_trans : transitive ca.
Proof. 
  (* TODO: generalize lemma *)
  rewrite /ca /transitive /= /dhrel_cnv. 
  move=> x y z /[swap]. apply rt_closure_trans.
Qed.

Arguments ca_trans {_ _ _}.

(* TODO: reformulate using notations of relation-algebra? *)
Lemma ca_po e1 e2 : ca e1 (fpo e2) -> ca e1 e2.
Proof. by move/ca_trans/(_ (ca_fpo _)). Qed.

Lemma ca_stepR e1 e3 :
  e1 != e3 ->
  ca e1 e3 ->
  exists e2, [&& ca e1 e2, ica e2 e3 & e2 <^i e3].
Proof.
  move/[swap]/closure_n1P; elim=> [/eqP//|] e2 {}e3.
  case: (eqVneq e2 e3)=> [-> _ //| neq23 I23 /closure_n1P C12 _ neq13].
  by exists e2; rewrite C12 I23 lt_neqAle neq23 ica_le.
Qed.

Lemma ca_fresh e : ca fresh_id e -> e = fresh_id.
Proof. by move/closure_n1P; elim=> // ?? /[swap] ? /[swap]-> /ica_fresh. Qed.

Lemma ca_fresh_contra e1 e2 :
  ca e1 e2 -> e2 != fresh_id -> e1 != fresh_id.
Proof. by move=> H; apply /contra_neq; move: H=> /[swap] -> /ca_fresh. Qed.

(*Lemma ca_dom e1 e2: ca e1 e2 -> (e1 \in dom) = false ->
  e1 = e2.
Proof.
  move/closureP; elim=> // x y I /closureP ? IH /[dup]/IH.
  move: I=> /[swap] .
Qed.*)

(* Strict (irreflexive) causality *)
Definition sca e1 e2 := (e2 != e1) && (ca e1 e2).

Lemma sca_def : forall e1 e2, sca e1 e2 = (e2 != e1) && (ca e1 e2).
Proof. done. Qed.

Lemma refl_ca : reflexive ca.
Proof. done. Qed.

Definition causal_orderMixin :=
  @LePOrderMixin _ ca sca sca_def refl_ca ca_anti (@ca_trans).

Canonical porderType := @POrderType tt E causal_orderMixin.

Definition lposetMixin :=
  @lPoset.lPoset.Mixin E L (Order.POrder.class porderType) lab.

Canonical lposetType := 
  @lPoset.lPoset.Pack L E (lPoset.lPoset.Class lposetMixin).

Definition ca_pideal e : {fset E} := 
  seq_fset tt (wsuffix fca_gt e).

Lemma ca_pideal_inE e1 e2 : 
  e1 \in (ca_pideal e2) = (ca e1 e2).
Proof. by rewrite seq_fsetE. Qed.

Definition dwFinPOrderMixin :=
  let cls := (Order.POrder.class porderType) in
  @DwFinPOrder.DwFinPOrder.Mixin E cls ca_pideal ca_pideal_inE.

(* ************************************************************************* *)
(*     Immediate Conflict                                                    *)
(* ************************************************************************* *)

Definition icf (e1 e2 : E) : bool :=
  [&& e1 != e2,
      fpo e1 == fpo e2 &
      lab (fpo e1) != \init].

Lemma icf_dom e1 e2 : icf e1 e2 -> e2 \in dom.
Proof.
  case/and3P; case: (boolP (e2 \in dom))=> // /[dup] /fpo_ndom->.
  case: (boolP (e1 \in dom))=> [/fpo_dom+++ Eq|/fpo_ndom-> ? /negP/[apply] //].
  by move/eqP: Eq=>-> /[swap]/negP/[apply]. 
Qed.

Lemma icf0 e : ~~ icf e \i0.
Proof. 
  rewrite /icf fpo0; apply /negP=> [/and3P []] ? /eqP-> /[!lab0]. 
  by rewrite eq_refl.
Qed.

Lemma icfxx x : icf x x = false.
Proof. by apply/and3P; case; rewrite eq_refl. Qed.

Hint Resolve icfxx : core.

Definition icf_irrefl : irreflexive icf := icfxx.

Lemma icf_sym : symmetric icf.
Proof. 
  by move=> ??; apply/and3P/and3P; case=> ? /eqP-> *; split; rewrite // eq_sym. 
Qed.

(* ************************************************************************* *)
(*     Conflict                                                              *)
(* ************************************************************************* *)

Definition cf e1 e2 : bool :=
  has id [seq icf x y | x <- wsuffix fca_gt e1, y <- wsuffix fca_gt e2].

Lemma cfP {e1 e2} :
  reflect (exists e1' e2', [/\ ca e1' e1, ca e2' e2 & icf e1' e2']) (cf e1 e2).
Proof.
  rewrite /ca /rt_closure /= /dhrel_cnv.
  apply/(iffP hasP) => [[? /allpairsPdep[x[y[]]]] | [x [y []]]].
  - by move=> ?? -> /= ?; exists x, y. 
  by exists (icf x y)=> //; rewrite allpairs_f.
Qed.

Lemma cf0 e : ~~ cf e \i0.
Proof.
  apply/negP. move=> /cfP [e1 [e2 []]].
  move=> /[swap] /ca0 /eqP -> ?. 
  by move /(elimN idP)=> H; apply /H/icf0. 
Qed.

Lemma cf_sym : symmetric cf.
Proof.
  apply: symmetric_from_pre=> e1 e2 /cfP [e1' [e2'] []].
  by move=> ???; apply/cfP; exists e2', e1'; rewrite icf_sym. 
Qed.

Lemma cf_hereditary e1 e2 e3 e4 :
  cf e1 e2 -> ca e1 e3 -> ca e2 e4 -> cf e3 e4.
Proof.
  move=> /cfP[e1' [e2'] [/ca_trans C1] /ca_trans C2 *].
  by apply/cfP; exists e1', e2'; rewrite C1 // C2.
Qed.

Lemma cf_hereditaryL e1 e2 e3 :
  cf e1 e2 -> ca e1 e3 -> cf e2 e3.
Proof. by move=> /cf_hereditary /[apply]; rewrite cf_sym=>->. Qed.

Lemma cf_hereditaryR e1 e2 e3 :
  cf e1 e2 -> ca e2 e3 -> cf e1 e3.
Proof. by rewrite cf_sym; apply: cf_hereditaryL. Qed.

Lemma icf_cf e1 e2 : icf e1 e2 -> cf e1 e2.
Proof. by move=> I; apply/cfP; exists e1, e2; rewrite !ca_refl I. Qed.

(* TODO: refactor proof *)
Lemma cfE e1 e2 : 
  cf e1 e2 = [|| icf e1 e2,
                 has (cf e1) (filter (fun x => e2 != x) (fca e2)) |
                 has (cf e2) (filter (fun x => e1 != x) (fca e1)) ].
Proof.
  apply/idP/idP; last first. 
  - case/or3P=> [/icf_cf //||] /hasP[e]; rewrite mem_filter=> /andP[_ /ica_ca].
    - by move/[swap]; apply: cf_hereditaryR.
    by move=> /[swap] /cf_hereditaryR /[apply]; rewrite cf_sym.
  case/cfP=> e1' [e2' []].
  case: (boolP (e1' == e1))=> [/eqP-> _|].
  - case: (boolP (e2' == e2))=> [/eqP->_->|]; first (apply/orP; by left).
    move/ca_stepR/[apply] => [[x /and3P[/cf_hereditaryR H N + /icf_cf/H]]].
    rewrite lt_neqAle=> /andP[] *.
    have-> //: has (cf e1) [seq x0 <- fca e2 | e2 != x0].
    apply/hasP; exists x=> //; rewrite mem_filter; apply/andP; split=> //.
    by rewrite eq_sym.
  move/ca_stepR/[apply] => [[x /and3P[++++ /icf_cf/cf_hereditary H]]].
  rewrite lt_neqAle eq_sym; move/H=> C ? /andP[? _] /C ?.
  have-> //: has (cf e2) [seq x0 <- fca e1 | e1 != x0].
  apply/hasP; exists x=> //; rewrite ?mem_filter 1?cf_sym //; exact/andP. 
Qed.

(* ************************************************************************* *)
(*     Read events read-from non-conflicting writes                          *)
(* ************************************************************************* *)

Definition rf_ncf_dom := 
  all (fun e => (frf e != e) ==> ~~ (cf e (frf e))) dom.

Hypothesis RFnCFd : rf_ncf_dom.

Lemma rf_ncf e : frf e != e -> cf e (frf e) = false.
Proof.
  move=> N. apply/negbTE/negP; case: (boolP (e \in dom)) => [D|nD].
  - move/allP/(_ _ D)/negP: RFnCFd; rewrite N; by apply/contra_not=>->.
  rewrite frf_ndom // => /cfP[e1 [e2 []]]; do 2 move/ca_ndom/(_ nD)/eqP->.
  by rewrite icfxx.
Qed.

Lemma cf_irrelf : irreflexive cf.
Proof.
  move=> m; apply/negbTE/negP. 
  elim/(@wfb_ind Ident.Order.disp E): m=> m IHm.
  suff: ~ cf m (fpo m).
  - move=> /negP /(contraNF id) C. 
    rewrite cfE. rewrite orbb icfxx //=. 
    case: ifP; case: ifP=>//=; try rewrite C=> //;  
      move=> ?; rewrite rf_ncf eq_sym //=. 
  move=> /cfP[x [y []]]; case: (eqVneq x m)=> [-> _|].
  - move=> C /[dup]/icf_dom /fpo_n0; case: (y =P \i0)=> [->|_ /(_ erefl)].
    - by rewrite (negbTE (icf0 _)).
    move/lt_le_trans/(_ (ca_le _ _ C))/[swap]/and3P.
    by case=> ? /eqP-> ? /[! (@ltxx _ E)].
  move/ca_stepR=> /[apply] [[z /and3P[/[swap]]]].
  rewrite icaE /= !inE => /pred2P[]-> Cx Le.
  - by move=> Cy /icf_cf/cf_hereditary/(_ Cx Cy); exact/IHm.
  move=> /ca_po Cy /icf_cf/cf_hereditary/(_ Cx Cy).
  rewrite cf_sym rf_ncf //=. 
  apply/eqP=> fE; by rewrite fE ltxx in Le.
Qed.

Definition dup_free := 
  injectiveb [ffun x : finsupp fed => fed (val x)].

Lemma dup_freeP : reflect {in dom &, injective fed} dup_free.
Proof.
  apply/(iffP (fsfun_injective_inP _ _))=> H ??;
  [rewrite -?fed_supp_mem|rewrite ?fed_supp_mem]; by move/H/[apply].
Qed.

End PORFEventStructureTheory.

Section PrimePORFEventStruct.

Context (E : identType) (L : labType).
Implicit Type es : (@porf_eventstruct E L).

Inductive prime_porf_eventstruct := 
  PrimeES es of (rf_ncf_dom es && dup_free es).

Arguments PrimeES {_}.

Coercion porf_eventstruct_of (pes : prime_porf_eventstruct) :=
  let '(PrimeES es _) := pes in es.

Canonical prime_subType := [subType for porf_eventstruct_of].

Lemma prime_inj : injective (porf_eventstruct_of).
Proof. exact: val_inj. Qed.

Lemma rf_ncf_dom_es (es : prime_porf_eventstruct) : rf_ncf_dom es.
Proof. by case: es=> /= ? /andP[]. Qed.

Variable (es : prime_porf_eventstruct).

Lemma hered_porfes :
  @hereditary (lposetType es) <=%O (cf es).
Proof. exact: cf_hereditaryR. Qed.

Definition prime_porfMixin := 
  @Prime.EventStruct.Mixin E L _ 
    (cf es) (cf_irrelf es (rf_ncf_dom_es es)) (cf_sym es) hered_porfes.

Canonical prime_porfPrime := 
  let base := lPoset.lPoset.class (lposetType es) in 
  let dw_mix := @dwFinPOrderMixin E L es in
  @Prime.EventStruct.Pack L E 
    (@Prime.EventStruct.Class E L base dw_mix (Ident.class E) 
                                  (Ident.mixin (Ident.class E)) 
                                  prime_porfMixin).

End PrimePORFEventStruct.

Notation "e '|-' a # b" := (cf e a b) (at level 10).
