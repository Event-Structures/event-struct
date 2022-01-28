From Coq Require Import Relations.
From RelationAlgebra Require Import lattice monoid rel boolean kat_tac.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat seq tuple.
From mathcomp Require Import eqtype choice order generic_quotient.
From mathcomp Require Import fintype finfun finset fingraph finmap zify.
From eventstruct Require Import utils rel relalg inhtype ident order.
From eventstruct Require Import lts lposet pomset pomset_lts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.
Local Open Scope fset_scope.
Local Open Scope ident_scope.
Local Open Scope lposet_scope.
Local Open Scope pomset_scope.

Module Lab.

Module Lab.
Section ClassDef.
Record mixin_of (T0 : Type) (b : Choice.class_of T0)
                (T := Choice.Pack b) := Mixin {
  bot : T;
  com : {fset T} -> T -> bool;
  cf  : rel T;
  is_write : pred T;
  is_read  : pred T;
  _ : forall w, reflect (exists ws r, w \in ws /\ com ws r) (is_write w);
  _ : forall r, reflect (exists ws, com ws r) (is_read r);
  _ : ~~ is_write bot;
  _ : ~~ is_read  bot;
}.

Set Primitive Projections.

Record class_of (T : Type) := Class {
  base   : Choice.class_of T;
  mixin  : mixin_of base;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Choice.class_of.

Structure type := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack :=
  fun b bT & phant_id (Choice.class bT) b => fun m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Canonical eqType.
Canonical choiceType.
Notation labType := type.
Notation LabType T m := (@pack T _ _ id m).
End Exports.

End Lab.

Export Lab.Exports.

Variant typ := Read | Write | ReadWrite | Undef.

Definition eq_typ : rel typ := 
  fun t1 t2 => match t1, t2 with
  | Read     , Read      => true
  | Write    , Write     => true
  | ReadWrite, ReadWrite => true
  | Undef, Undef         => true
  | _ , _                => false
  end.

Lemma eq_typP : Equality.axiom eq_typ.
Proof. by case; case; constructor. Qed.

Module Export Def.
Section Def.
Context {L : labType}.
Implicit Types (l : L).

Definition bot : L := Lab.bot (Lab.class L).

Definition com : {fset L} -> L -> bool := Lab.com (Lab.class L).

Definition cf : rel L := Lab.cf (Lab.class L).

Definition is_write : pred L := Lab.is_write (Lab.class L).
Definition is_read  : pred L := Lab.is_read  (Lab.class L).

Canonical typ_eqMixin := EqMixin eq_typP.
Canonical typ_eqType  := Eval hnf in EqType typ typ_eqMixin.

Definition lab_typ l : typ := 
  if is_read l && ~~ is_write l then 
    Read 
  else if is_write l && ~~ is_read l then 
    Write
  else if is_read l && is_write l then 
    ReadWrite
  else Undef.

End Def.
End Def.

Module Export Syntax.
Notation "ls '|-' l"  := (com ls l) (at level 90).
Notation "l1 '\#' l2" := (cf l1 l2) (at level 90).
End Syntax.

Module Export Theory.
Section Theory.
Context (L : labType).
Implicit Types (l r w: L).

Lemma is_writeP w : 
  reflect (exists ws r, w \in ws /\ com ws r) (is_write w).
Proof. by move: w; case L=> ? [? []]. Qed.

Lemma is_readP r : 
  reflect (exists ws, com ws r) (is_read r).
Proof. by move: r; case L=> ? [? []]. Qed.

Lemma bot_nwrite : 
  ~~ is_write (bot : L).
Proof. by case L=> ? [? []]. Qed.

Lemma bot_nread : 
  ~~ is_read (bot : L).
Proof. by case L=> ? [? []]. Qed.

End Theory.
End Theory.

End Lab.

Export Lab.Lab.Exports.
Export Lab.Def.
Export Lab.Syntax.
Export Lab.Theory.


Module Export ThrdPomset.

Notation thrd_pomset E L Tid := 
  (@pomset E _ (\i0 : Tid, bot : L)).

Notation thrd_pomlang E L Tid := 
  (@pomset E _ (\i0 : Tid, bot : L) -> Prop).

Section Def.
Context {E : identType} {L : labType}.
Context {Tid : identType}.
(* data-type semantics *)
Context (DS : ltsType L).
(* thread semantics *)
Context (TS : ltsType L).
Implicit Types (d : DS) (s : TS).
Implicit Types (p q : @thrd_pomset E L Tid).

Definition fs_tid p e := 
  fst (fs_lab p e).

Definition fs_tids p := 
  [fset (fs_tid p e) | e in finsupp p].

Definition fs_dlab p e := 
  snd (fs_lab p e).

Definition fs_typ p e := 
  lab_typ (fs_dlab p e).

Definition dlab_defined p := 
  [forall e : finsupp p, fs_dlab p (val e) != bot].

Definition lab_prj : Tid * L -> L := snd.

Definition lts_thrd_pomlang d : thrd_pomlang E L Tid := 
  fun p => (lts_pomlang d : pomlang E L bot) (Pomset.relabel lab_prj p).

Definition respects_com d : thrd_pomlang E L Tid := 
  fun p => forall e, exists (es : {fset E}), 
    [/\ (fs_dlab p) @` es |- (fs_dlab p e)
      & forall e', e' \in es -> e' <= e :> [Event of p]
    ].

Definition cf_commute d := forall (u v : seq L) (a b : L), 
  let Dlang := lts_lang d in
  ~ (a \# b) -> (Dlang (u ++ [:: a ; b] ++ v) <-> Dlang (u ++ [:: b ; a] ++ v)).

Lemma lab_prj_bot :
  lab_prj (\i0, bot) = bot.
Proof. done. Qed.

End Def.

End ThrdPomset.

Section ProgramOrder.
Context {E : identType} {L : labType}.
Context {Tid : identType}.
(* thread semantics *)
Context (TS : ltsType L).
Implicit Types (p q : @thrd_pomset E L Tid).

Definition eq_tid p : rel E := 
  fun e1 e2 => fs_tid p e1 == fs_tid p e2.

Arguments eq_tid p : clear implicits. 

Lemma eqtid_refl p : reflexive (eq_tid p).
Proof. by rewrite /eq_tid. Qed.

Lemma eqtid_sym p : symmetric (eq_tid p).
Proof. by rewrite /eq_tid. Qed.

Lemma eqtid_trans p : transitive (eq_tid p).
Proof. by rewrite /eq_tid=> ??? /eqP-> /eqP->. Qed.

Definition po p : thrd_pomset E L Tid := 
  Pomset.inter_rel (eq_tid p) (@eqtid_refl p) (@eqtid_trans p) p.

Definition po_spec p := 
  {in (fs_tids p), forall t, exists (s0 : TS),
    let es := [fset e | e in finsupp p & (fs_tid p e == t)] in
    let pt := Pomset.restrict (mem es) p in
    (lts_pomlang s0 : pomlang E L bot) (Pomset.relabel lab_prj pt)
  }.

End ProgramOrder.


Section SeqCst.
Context {E : identType} {L : labType}.
Context {Tid : identType}.
(* data-type semantics *)
Context (DS : ltsType L).
(* thread semantics *)
Context (TS : ltsType L).

Implicit Types (d : DS) (s : TS).
Implicit Types (p q : @thrd_pomset E L Tid).

Definition seq_cst d p := 
  eq (po p) \supports (lts_thrd_pomlang d).

End SeqCst.

(* TODO: better name? *)
Section ValueRelab. 
Context {E : identType} {L : labType}.
Context {Tid : identType}.
(* data-type semantics *)
Context (DS : ltsType L).
(* thread semantics *)
Context (TS : ltsType L).
Implicit Types (p : @thrd_pomset E L Tid).

(* checks that f is a value-relabeling of pomset p w.r.t. set of events es *)
Definition relab_mod p (es : {fset E}) (f : Tid * L -> L) := 
  let lab e  := fs_lab  p (val e) in
  let dlab e := fs_dlab p (val e) in
  [&& (* types of all events are preserved (i.e. reads/writes are preserved) *)
      [forall e : finsupp p, lab_typ (f (lab e)) == lab_typ (dlab e)]
    , (* conflict relation is preserved *)
      [forall e1 : finsupp p, forall e2 : finsupp p, 
        (f (lab e1) \# f (lab e2)) == ((dlab e1) \# (dlab e2)) 
      ]
    & (* labels of all events not in es are preserved *)
      [forall e : finsupp p, (val e \notin es) ==> (f (lab e) == dlab e)]
  ].

End ValueRelab. 


Section CausalCst. 
Context {E : identType} {L : labType}.
Context {Tid : identType}.
(* data-type semantics *)
Context (DS : ltsType L).
(* thread semantics *)
Context (TS : ltsType L).

Implicit Types (d : DS) (s : TS).
Implicit Types (p : @thrd_pomset E L Tid).

(* Causally relabeled threaded pomset language of data-structure DS.
 * Pomset p belongs to this language if 
 * for every event e of p, the restriction of p onto prefix of e
 * is equiavelnt to relabeling of some q \in (lang DS) such that this relabeling
 *   (1) preserves labels of all events from the thread of e 
 *       and all writes events (i.e. non-reads);
 *   (2) preserves types (i.e. reads/writes) of all events.
 *)
Definition causal d p := 
  {in (finsupp p), forall e, exists f,
    let rst := pideal (e : [Event of p]) in
    let ro := 
      [fset e' in finsupp p | (fs_typ p e' == Lab.Read) && ~~ (eq_tid p e e')]
    in
    let p_rlb := Pomset.relabel f p in  
    let p_rst := Pomset.restrict (mem rst) p_rlb in
    [/\ relab_mod p ro f
      & eq (p_rst) \supports (lts_pomlang d : pomlang E L bot)
    ]
  }.
  
Definition causal_cst d p := 
  eq (po p) \supports (causal d).  


End CausalCst.


Section PipeCst. 
Context {E : identType} {L : labType}.
Context {Tid : identType}.
(* data-type semantics *)
Context (DS : ltsType L).
(* thread semantics *)
Context (TS : ltsType L).

Implicit Types (d : DS) (s : TS).
Implicit Types (p : @thrd_pomset E L Tid).

Definition pipe_cst d p := 
  {in (fs_tids p), forall t, exists f,
    let prv := 
      [fset e' in finsupp p | (fs_tid p e' == t) || ~~ is_read (fs_dlab p e')]
    in
    let po_rlb := Pomset.relabel f (po p) in  
    [/\ relab_mod p prv f
      & eq po_rlb \supports (lts_pomlang d : pomlang E L bot)
    ]
  }.

End PipeCst.
