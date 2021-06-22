From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From mathcomp Require Import choice eqtype order.
From eventstruct Require Import utils wftype.

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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.
Open Scope order_scope.

Declare Scope ident_scope.
Delimit Scope ident_scope with ident.

Local Open Scope ident_scope.

(* Notation for initial identifier *)
Reserved Notation "\i0" (at level 0).

(* Notations for canonical order on identifiers *)
Reserved Notation "x <=^i y" (at level 70, y at next level).
Reserved Notation "x >=^i y" (at level 70, y at next level).
Reserved Notation "x <^i y" (at level 70, y at next level).
Reserved Notation "x >^i y" (at level 70, y at next level).
Reserved Notation "x <=^i y :> T" (at level 70, y at next level).
Reserved Notation "x >=^i y :> T" (at level 70, y at next level).
Reserved Notation "x <^i y :> T" (at level 70, y at next level).
Reserved Notation "x >^i y :> T" (at level 70, y at next level).
Reserved Notation "<=^i y" (at level 35).
Reserved Notation ">=^i y" (at level 35).
Reserved Notation "<^i y" (at level 35).
Reserved Notation ">^i y" (at level 35).
Reserved Notation "<=^i y :> T" (at level 35, y at next level).
Reserved Notation ">=^i y :> T" (at level 35, y at next level).
Reserved Notation "<^i y :> T" (at level 35, y at next level).
Reserved Notation ">^i y :> T" (at level 35, y at next level).
Reserved Notation "x >=<^i y" (at level 70, no associativity).
Reserved Notation ">=<^i y" (at level 35).
Reserved Notation ">=<^i y :> T" (at level 35, y at next level).
Reserved Notation "x ><^i y" (at level 70, no associativity).
Reserved Notation "><^i x" (at level 35).
Reserved Notation "><^i y :> T" (at level 35, y at next level).

Section Utils. 
Context {T : countType}.

Lemma pickle_inj : injective (@pickle T).
Proof. by apply /pcan_inj /pickleK. Qed.

End Utils.

Module Ident.
Section ClassDef.

Record mixin_of T0 (b : Countable.class_of T0)
  (T := Countable.Pack b) := Mixin {
  _ : forall n, @unpickle T n;

  (* fresh : T -> T; *)
  (* ident0 : T; *)
  (* _ : forall x, ident0 <= x; *)
  (* _ : forall x, x < fresh x; *)
}.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base  : Countable.class_of T;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Countable.class_of.

Structure type := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack :=
  fun bT b & phant_id (@Countable.class bT) b =>
  fun m => Pack (@Class T b m).

(* Inheritance *)
(* Definition wfType := @WellFounded.Pack disp cT class. *)
(* Definition porderType := @Order.POrder.Pack disp cT class. *)
Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition countType := @Countable.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Countable.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
(* Coercion porderType : type >-> Order.POrder.type. *)
(* Coercion wfType : type >-> WellFounded.type. *)

Canonical eqType.
Canonical choiceType.
Canonical countType.
(* Canonical wfType. *)
(* Canonical porderType. *)

Notation identType := type.
Notation IdentType disp T m := (@pack T disp _ _ id m).
Notation "[ 'identType' 'of' T 'for' cT ]" := (@clone T cT _ id)
  (at level 0, format "[ 'identType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'identType' 'of' T ]" := [identType of T for _]
  (at level 0, format "[ 'identType'  'of'  T ]") : form_scope.
End Exports.

Module Export Def.

Definition unpickle_tot {T : identType} n : @unpickle T n. 
Proof. by case: T=> ? [? []]. Defined.

Notation encode (* : T -> nat *) := (pickle).
Notation decode (* : nat -> T *) := (mk_total unpickle_tot).

Section Def.
Context {T : identType}.

Definition ident0 : T := 
  decode 0.

Definition fresh : T -> T := 
  fun x => decode (1 + encode x).

Definition fresh_seq : seq T -> T := 
  fun s => decode (1 + foldl maxn 0 (map encode s)).

Definition ident_le : rel T := 
  fun x y => encode x <= encode y.

Definition ident_lt : rel T := 
  fun x y => encode x < encode y.

Definition ident_min : T -> T -> T := 
  fun x y => decode (minn (encode x) (encode y)).

Definition ident_max : T -> T -> T := 
  fun x y => decode (maxn (encode x) (encode y)).

End Def.
End Def. 

Prenex Implicits fresh fresh_seq ident_le ident_lt.

Module Order. 
Section Order. 

Context (T : identType).
Implicit Types (x y z : T).

Lemma idisp : unit. 
Proof. exact: tt. Qed.

Lemma lt_def x y : (ident_lt x y) = (y != x) && (ident_le x y).
Proof. 
  rewrite /ident_lt /ident_le. 
  have ->: (y != x) = (pickle y != pickle x); last exact /lt_def. 
  case H: (y == x); first by (move: H=> /eqP->; rewrite eq_refl).
  move=> /=; apply esym.
  move: H=> /eqP /eqP /=. 
  by apply /contra_neq /pickle_inj.
Qed.

Lemma meet_def x y : ident_min x y = (if ident_lt x y then x else y).
Proof. 
  rewrite /ident_min /ident_lt /minn /Order.lt=> /=.
  rewrite (mk_totalE ident0).
  by case: ifP=> ?; rewrite pickleK /=. 
Qed.

Lemma join_def x y : ident_max x y = (if ident_lt x y then y else x).
Proof. 
  rewrite /ident_max /ident_lt /maxn /Order.lt=> /=.
  rewrite (mk_totalE ident0).
  by case: ifP=> ?; rewrite pickleK /=. 
Qed.

Lemma le_anti : antisymmetric (@ident_le T). 
Proof. 
  move=> x y /andP []; rewrite /ident_le=> ??.
  by apply /pickle_inj /anti_leq /andP. 
Qed.

Lemma le_trans : transitive (@ident_le T). 
Proof. by move=> z x y; rewrite /ident_le; apply leq_trans. Qed.

Lemma le_total : total (@ident_le T). 
Proof. by move=> x y; rewrite /ident_le; apply leq_total. Qed.

Lemma encodeK : cancel decode (encode : T -> nat).
Proof. 
  move=> x; rewrite /decode.
  move: (unpickle_tot x). 
  case H: (unpickle x)=> [{}y|] //.
  rewrite /finmap.oextract=> ?; move: H.
  have ->: (Some y = unpickle (pickle y)).
  - apply /esym /pickleK. 
  admit. 
Admitted.  

Lemma encode0 : encode (ident0 : T) = 0.
Proof. by rewrite /ident0 encodeK. Qed.

Lemma le0x x : ident_le ident0 x.
Proof. by rewrite /ident_le encode0; apply leq0n. Qed.

Definition mixin :=
  LeOrderMixin lt_def meet_def join_def le_anti le_trans le_total.

End Order.

Module Export Exports.
(* Context {T : identType}. *)

Canonical porderType {T : identType} := POrderType idisp T (@Order.mixin T).
(* Canonical latticeType := LatticeType T (@Order.mixin T). *)
(* Canonical bLatticeType := BLatticeType T (BottomMixin (@Order.le0x T)). *)
(* Canonical distrLatticeType := DistrLatticeType T (@Order.mixin T). *)
(* Canonical bDistrLatticeType := [bDistrLatticeType of T]. *)
(* Canonical orderType := OrderType T (@Order.mixin T). *)

End Exports.

Context {T : identType} (a b : T).

End Order.

Module Syntax. 
Notation "'\i0'" := (ident0).
End Syntax.

End IdentType.

Export IdentType.Exports.
Export IdentType.Def.
Export IdentType.Syntax.

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

