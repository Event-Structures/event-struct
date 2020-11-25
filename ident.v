From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import order choice finmap.
From Coq Require Import ssrsearch.
From event_struct Require Import wftype.

(******************************************************************************)
(* This file contains the definitions of:                                     *)
(*   identType d == interface for inhabited types with decidable equality     *)
(*               equipped with a monotone (w.r.t some wellfounded strict      *)
(*               relation) function                                           *)
(*      fresh id == a fresh identifier coming after id.                       *)
(*        ident0 == an initial identifier.                                    *)
(*      nfresh n == nth fresh itendificator (strating with ident0)            *)
(*      nfresh_seq n == a sequence of size n of fresh identifiers             *)
(*                  starting with ident0.                                     *)
(*      nfresh_set n == a set of size n of fresh identifiers                  *)
(*                  starting with ident0.                                     *)
(* This file also contains definitions of a Canonical identType instance for  *)
(* nat.                                                                       *)
(******************************************************************************)

Import Order.LTheory.
Open Scope order_scope.
Open Scope fset_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module IdentType.

Section ClassDef.

Record mixin_of T0 (b : WellFounded.class_of T0)
  (T := WellFounded.Pack tt b) := Mixin {
  fresh : T -> T;
  ident0 : T;
  _ : forall x, x < fresh x;
}.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base  : WellFounded.class_of T;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> WellFounded.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : (type disp)).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.

Definition pack :=
  fun bT b & phant_id (@WellFounded.class disp bT) b =>
  fun m => Pack disp (@Class T b m).

(* Inheritance *)
Definition wfType := @WellFounded.Pack disp cT class.
Definition porderType := @Order.POrder.Pack disp cT class.
Definition choiceType := @Choice.Pack cT class.
Definition eqType := @Equality.Pack cT class.
End ClassDef.

Module Exports.
Coercion base : class_of >-> WellFounded.class_of.
Coercion sort : type >-> Sortclass.
Coercion wfType : type >-> WellFounded.type.
Coercion porderType : type >-> Order.POrder.type.
Coercion choiceType : type >-> Choice.type.
Coercion eqType : type >-> Equality.type.
Canonical wfType.
Canonical porderType.
Canonical choiceType.
Canonical eqType.
Notation identType := type.
Definition fresh {disp} {T : identType disp} : T -> T := fresh (mixin (class T)).
Definition ident0 {disp} {T : identType disp} : T := ident0 (mixin (class T)).
Notation IdentType disp T m := (@pack T disp _ _ id m).
Notation "[ 'identType' 'of' T 'for' cT ]" := (@clone T cT _ id)
  (at level 0, format "[ 'identType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'identType' 'of' T ]" := [identType of T for _]
  (at level 0, format "[ 'identType'  'of'  T ]") : form_scope.
End Exports.

End IdentType.
Export IdentType.Exports.

Section IdentTheory.
Context {disp} {T : identType disp}.
Local Notation ident0 := (@ident0 disp T).
Local Notation fresh := (@fresh disp T).

Definition nfresh n := iter n fresh ident0.

Definition nfresh_seq n := rev (traject fresh ident0 n).

Definition nfresh_set n := seq_fset tt (nfresh_seq n).

Lemma fresh_lt x : x < fresh x. Proof. by case: T x=> ? [/= ? []]. Qed.

Lemma sorted_nfresh n : sorted (>%O) (nfresh_seq n).
Proof.
  elim n=> // m; rewrite /nfresh_seq trajectSr rev_rcons.
  case: m=> // ?; by rewrite trajectSr rev_rcons /= fresh_lt.
Qed.

Lemma uniq_nfresh_seq n: uniq (nfresh_seq n).
Proof.
  apply/(sorted_uniq _ _ (sorted_nfresh _)).
  - exact/rev_trans/lt_trans.
  exact/lt_irreflexive.
Qed.

Lemma nfresh_seqS n: nfresh_seq n.+1 = (nfresh n) :: nfresh_seq n.
Proof. by rewrite /nfresh_seq trajectSr rev_rcons. Qed.

Lemma nfresh_setS n : nfresh_set n.+1 = nfresh n |` nfresh_set n.
Proof.
  apply/fsetP=> ?.
  by rewrite /nfresh_set nfresh_seqS ?(inE, seq_fsetE).
Qed.

Lemma size_nfresh_seq n: size (nfresh_seq n) = n.
Proof. by elim n=> //= ? {2}<-; rewrite nfresh_seqS. Qed.

Lemma size_nfresh_set n: #|`nfresh_set n| = n.
Proof. 
  by rewrite size_seq_fset undup_id (size_nfresh_seq, uniq_nfresh_seq). 
Qed.

End IdentTheory.

Import Order.NatOrder.

Section IdentDataTypes.

Definition nat_identMixin :=
  @IdentType.Mixin nat (WellFounded.class nat_wfType) succn 0 ltnSn.

End IdentDataTypes.

Canonical nat_identType := 
  Eval hnf in IdentType nat_display nat nat_identMixin.

(*Eval cbv in (@nfresh_seq nat_display nat_identType 5).*)

(* Definition of wfidentType *)
