From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import order choice.
From event_struct Require Import utilities wftype.

(******************************************************************************)
(* This file contains the definitions of:                                     *)
(*  identType d == interface for inhabited well-founded orders equipped with  *)
(*                 increasing function to generate "fresh" identifiers.       *)
(*     fresh id == a fresh identifier coming after id (id < fresh id).        *)
(*       \i0 == an initial identifier.                                     *)
(*     nfresh n == a decreasing sequence of size n+1 of fresh identifiers     *)
(*                 with \i0 as the last element.                           *)
(*  fresh_seq s == an identifier fresher than the head of the s sequence      *)
(*                 (\i0 if s is empty). Helps with reducing time           *)
(*                 complexity of incremental generation of sequences of fresh *)
(*                 identifiers).                                              *)
(* This file also contains canonical instance of identType for nat.           *)
(******************************************************************************)

Import Order.LTheory.
Open Scope order_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module IdentType.

Section ClassDef.

Record mixin_of T0 (b : WellFounded.class_of T0)
  (T := WellFounded.Pack tt b) := Mixin {
  fresh : T -> T;
  ident0 : T;
  _ : forall x, ident0 <= x;
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

Notation "'\i0'" := (@ident0 _ _).

Section IdentTheory.
Context {disp} {T : identType disp}.
Local Notation ident0 := (@ident0 disp T).
Local Notation fresh := (@fresh disp T).

Lemma fresh_lt x : x < fresh x.
Proof. by case: T x=> ? [/= ? []]. Qed.

Lemma fresh_iter n m x: iter n fresh x = iter m fresh x -> n = m.
Proof.
  have F: forall x n, x < iter n.+1 fresh x.
  - move=> {x}{n}x; elim=> /= [|? /lt_trans]; last apply; exact/fresh_lt.
  elim: n m x=> /= [[] // n x|n IHn [/= x|l x]].
  - move: (F x n)=>/[swap]{1}->; by rewrite ltxx.
  - rewrite -iterS; move: (F x n)=>/[swap]{1}->; by rewrite ltxx.
  by rewrite -iterS ?iterSr => /IHn->.
Qed.

Lemma i0_le (x : T) : \i0 <= x.
Proof. by case: T x=> ? [/= ? []]. Qed.

Lemma i0_mem (s : seq T): 
  \i0 \notin s = all (> \i0) s.
Proof.
  elim: s=> //= a ? <-; rewrite ?inE.
  case: (\i0 \in _)=> //=; rewrite (orbF, orbT) (andbF, andbT) //.
  have C: (\i0 >=< a) by rewrite /(_ >=< _) (i0_le _).
  move: (i0_le a); by case: (comparable_ltgtP C).
Qed.

Definition fresh_seq s := fresh (head \i0 s).

Lemma i0_fresh_seq s: \i0 < fresh_seq s.
Proof.
  case: s=> [|??]; first exact/fresh_lt.
  exact/(le_lt_trans _ (fresh_lt _))/i0_le.
Qed.

Section Add_Sorted.

Context {s : seq T} (s_sorted : sorted (>%O) s).

Lemma path_fresh_seq : path (>%O) (fresh_seq s) s.
Proof. by case: s s_sorted=> //= ??; rewrite fresh_lt. Qed.

Lemma fresh_seq_lt x : x \in s -> x < fresh_seq s.
Proof.
  move: path_fresh_seq; rewrite path_sortedE.
  - by case/andP=> /allP + _ => /[apply].
  exact/rev_trans/lt_trans.
Qed.

Lemma fresh_seq_le x : x \in (fresh_seq s :: s) -> x <= fresh_seq s.
Proof. by rewrite inE=> /predU1P[->|/fresh_seq_lt/ltW]. Qed.

Lemma fresh_seq_notin : fresh_seq s \notin s.
Proof. by apply/memPn => x /fresh_seq_lt; rewrite lt_neqAle=> /andP[]. Qed.

End Add_Sorted.


Definition nfresh n := iter n (fun s => fresh_seq s :: s) [:: \i0].

Lemma nfreshS n : nfresh n.+1 = fresh_seq (nfresh n) :: (nfresh n).
Proof. by []. Qed.

Lemma fresh_seq_iter n : fresh_seq (nfresh n) = iter n.+1 fresh \i0.
Proof. by elim: n=> //= ? ->. Qed.

Section NfreshSpec.

Lemma nfresh_sorted n : sorted (>%O) (nfresh n).
Proof. by elim: n=> //= n IHn; rewrite path_fresh_seq. Qed.

Lemma nfreshE n : nfresh n = rev (traject fresh \i0 n.+1).
Proof.
  by elim: n=> // n IHn; rewrite nfreshS fresh_seq_iter trajectSr rev_rcons IHn.
Qed.

Lemma nfresh_size n : size (nfresh n) = n.+1.
Proof. by rewrite nfreshE size_rev size_traject. Qed.

Lemma nfresh_last n : last \i0 (nfresh n) = \i0.
Proof. by rewrite nfreshE trajectS rev_cons -cats1 last_cat. Qed.

End NfreshSpec.

Lemma nfresh_le x n : x \in nfresh n.+1 -> x <= fresh_seq (nfresh n).
Proof. by move=> /= /fresh_seq_le; apply; apply: nfresh_sorted. Qed.

End IdentTheory.

Import Order.NatOrder.

Section IdentDataTypes.

Definition nat_identMixin :=
  @IdentType.Mixin nat (WellFounded.class nat_wfType) succn 0 leq0n ltnSn.

End IdentDataTypes.

Canonical nat_identType :=
  Eval hnf in IdentType nat_display nat nat_identMixin.

