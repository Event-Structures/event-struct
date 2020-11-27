From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import order choice finmap.
From event_struct Require Import wftype utilities.

(******************************************************************************)
(* This file contains the definitions of:                                     *)
(*   identType d == interface for inhabited types with decidable equality     *)
(*               equipped with a monotone (w.r.t some wellfounded strict      *)
(*               relation) function                                           *)
(*      fresh id == a fresh identifier coming after id.                       *)
(*        ident0 == an initial identifier.                                    *)
(*      fresh_seq s == fresh h, where h is the head of s, or fresh ident0 if  *)
(*                  s is empty                                                *)
(*      nfresh n == a sequence of size n of fresh identifiers                 *)
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

Lemma fresh_lt x : x < fresh x. Proof. by case: T x=> ? [/= ? []]. Qed.

Definition fresh_seq s := fresh (head ident0 s).

Section Add_Sorted.

Context {s : seq T} (s_sorted : sorted (>%O) s).

Lemma path_fresh_seq: path (>%O) (fresh_seq s) s.
Proof.
  case: s s_sorted=> //= ??->.
  by rewrite /fresh_seq /= fresh_lt.
Qed.

Lemma fresh_seq_lt x : x \in s -> x < fresh_seq s.
Proof.
  move: path_fresh_seq; rewrite path_sortedE.
  - by case/andP=>/swap ? /allP /apply.
  exact/rev_trans/lt_trans.
Qed.

Lemma fresh_seq_le x: x \in (fresh_seq s :: s) -> x <= fresh_seq s.
Proof. by rewrite ?inE => /orP[/eqP->|/fresh_seq_lt/ltW]. Qed.

End Add_Sorted.

Definition nfresh n := iter n (fun s => fresh_seq s :: s) [:: ident0].

Lemma nfreshS n: nfresh n.+1 = fresh_seq (nfresh n) :: (nfresh n).
Proof. by []. Qed.

Lemma fresh_seq_iter n: fresh_seq (nfresh n) = iter n.+1 fresh ident0.
Proof. by elim: n=> //= ? ->. Qed.

Lemma nfesh_le x n: x \in nfresh n.+1 -> x <= fresh_seq (nfresh n).
Proof.
  elim n=> //= [|? IHn]; rewrite ?inE=> /orP[/eqP-> //|].
  - move/eqP->; exact/(ltW (fresh_lt _)).
  by rewrite {2}/fresh_seq /= => /IHn /le_trans/(_ (ltW (fresh_lt _))).
Qed.

End IdentTheory.

Import Order.NatOrder.

Section IdentDataTypes.

Definition nat_identMixin :=
  @IdentType.Mixin nat (WellFounded.class nat_wfType) succn 0 ltnSn.

End IdentDataTypes.

Canonical nat_identType := 
  Eval hnf in IdentType nat_display nat nat_identMixin.

(*Eval cbv in (@nfresh nat_display nat_identType 5).*)

(* Definition of wfidentType *)
