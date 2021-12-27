From Coq Require Import Relations.
From RelationAlgebra Require Import lattice monoid rel boolean kat_tac.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat seq tuple.
From mathcomp Require Import eqtype choice order.
From mathcomp Require Import fintype finfun finset fingraph finmap zify.
From eventstruct Require Import utils rel relalg inhtype ident.
From eventstruct Require Import lts lposet pomset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.
Local Open Scope fset_scope.
Local Open Scope ident_scope.
Local Open Scope lposet_scope.
Local Open Scope pomset_scope.

Module Export Lab.

Module Lab.
Section ClassDef.
Record mixin_of (T0 : Type) (b : Choice.class_of T0)
                (T := Choice.Pack b) := Mixin {
  bot : T;
  com : rel T;
  is_write : pred T;
  is_read  : pred T;
  _ : forall w, reflect (exists r, com w r) (is_write w);
  _ : forall r, reflect (exists w, com w r) (is_read  r);
  _ : ~~ is_write bot;
  _ : ~~ is_read  bot;
  (* TODO: add requirement that com is functional? *)
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

Section Def.
Context {L : labType}.
Implicit Types (l : L).

Definition bot : L := Lab.bot (Lab.class L).

Definition com : rel L := Lab.com (Lab.class L).

Definition is_write : pred L := Lab.is_write (Lab.class L).
Definition is_read  : pred L := Lab.is_read  (Lab.class L).

End Def.

Module Export Syntax.
Notation "l1 '\>>' l2" := (com l1 l2) (at level 90).
End Syntax.

Section Theory.
Context (L : labType).
Implicit Types (l r w: L).

Lemma is_writeP w : 
  reflect (exists r, com w r) (is_write w).
Proof. by move: w; case L=> ? [? []]. Qed.

Lemma is_readP r : 
  reflect (exists w, com w r) (is_read r).
Proof. by move: r; case L=> ? [? []]. Qed.

Lemma bot_nwrite : 
  ~~ is_write (bot : L).
Proof. by case L=> ? [? []]. Qed.

Lemma bot_nread : 
  ~~ is_read (bot : L).
Proof. by case L=> ? [? []]. Qed.

End Theory.

End Lab.


Section ProgramOrder.
Context {E : identType} {L : labType}.
Context {Tid : identType}.
(* thread semantics *)
Context (TS : ltsType L).
Implicit Types (p q : @pomset E _ (\i0 : Tid, bot : L)).

Definition eqtid p : rel [Event of p] := 
  fun e1 e2 => fst (lab e1) == fst (lab e2).

Arguments eqtid p : clear implicits. 

Lemma eqtid_refl p : reflexive (eqtid p).
Proof. by rewrite /eqtid. Qed.

Lemma eqtid_sym p : symmetric (eqtid p).
Proof. by rewrite /eqtid. Qed.

Lemma eqtid_trans p : transitive (eqtid p).
Proof. by rewrite /eqtid=> ??? /eqP-> /eqP->. Qed.

Definition lab_prj : Tid * L -> L := snd.

Lemma lab_prjD l :
  (l == (\i0, bot)) = (lab_prj l == bot).
Proof using. 
  case: l=> t l; rewrite /lab_prj xpair_eqE /=.
  admit.
Admitted.

Definition po p := 
  let q := Pomset.inter_rel (eqtid p) (@eqtid_refl p) (@eqtid_trans p) p in
  Pomset.relabel p lab_prjD. 

(* Definition po_total p :=  *)
(*   totalb (fin_ca (po p)). *)

End ProgramOrder.

Section SeqCst.
Context {E : identType} {L : labType}.
Context {Tid : identType}.
(* data-type semantics *)
Context (DS : ltsType L).
(* thread semantics *)
Context (TS : ltsType L).

Implicit Types (d : DS) (s : TS).
Implicit Types (p q : @pomset E _ (\i0 : Tid, bot : L)).

Definition seq_cst d p := 
  (eq (po p) : pomlang E L bot) \supports (@lts_pomlang E L bot _ d).

End SeqCst.
