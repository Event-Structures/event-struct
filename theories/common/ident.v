From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq path.
From mathcomp Require Import choice eqtype order.
From eventstruct Require Import utils ssrnatlia wftype countable.

(******************************************************************************)
(* This file contains a theory of types that can be used as identifiers.      *)
(* Essentially, a type of identifiers is an infinite countable type.          *)
(*                                                                            *)
(*  identType  == interface for types which behave as identifiers.            *)
(*    \i0, \i1 == some distinguished identifiers.                             *)
(*     fresh i == allocates a fresh identifier which is guaranteed to         *)
(*                differ from i.                                              *) 
(*  nfresh i n == allocates n fresh identifier which are guaranteed to        *)
(*                differ from i.                                              *)
(* fresh_seq s == allocates a fresh identifier which is guaranteed to         *)
(*                differ from all identifiers from the list s                 *)
(*                                                                            *)
(* Elements of identType also can be converted to natural numbers and back    *)
(* from natural numbers. This conversion also induces a total well-founded    *)
(* order on identifiers.                                                      *)
(*    encode i == converts the identifier i into a natural number.            *)
(*    decode n == converts the natural number n into an identifier.           *)
(*    x <=^i y == a total well-founded order on identifiers induced           *)
(*                by the conversion to natural numbers.                       *)
(*                That is x <=^i y iff encode x <= encode y.                  *)
(*                All conventional order notations are defined with           *)
(*                the suffix _^i as well.                                     *)
(*                                                                            *)
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
Reserved Notation "\i1" (at level 0).

Module Ident.
Section ClassDef.

Record mixin_of T0 (b : Countable.class_of T0)
  (T := Countable.Pack b) := Mixin {
  _ : forall n, @unpickle T n;
  _ : injective (@unpickle T)
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

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition countType := @Countable.Pack cT class.

Local Notation disp := (countable.Order.disp).

Definition porderType := 
  @Order.POrder.Pack disp cT (Order.POrder.class countType).
Definition latticeType := 
  @Order.Lattice.Pack disp cT (Order.Lattice.class countType).
Definition distrLatticeType := 
  @Order.DistrLattice.Pack disp cT (Order.DistrLattice.class countType).
Definition wfType := 
  @WellFounded.Pack disp cT (WellFounded.class countType).

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Countable.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Coercion porderType : type >-> Order.POrder.type.
Coercion latticeType : type >-> Order.Lattice.type.
Coercion distrLatticeType : type >-> Order.DistrLattice.type.
Coercion wfType : type >-> WellFounded.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical porderType.
Canonical latticeType.
Canonical distrLatticeType.
Canonical wfType.
Notation identType := type.
Notation IdentType T m := (@pack T _ _ id m).
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
  decode 0%nat.

Definition ident1 : T := 
  decode 1%nat.

Definition fresh : T -> T := 
  fun x => decode (1 + encode x).

Definition nfresh : T -> nat -> seq T := 
  fun i n => traject fresh i n. 

Definition fresh_seq : seq T -> T := 
  fun s => decode (1 + foldl maxn 0 (map encode s)).

End Def.
End Def. 

Prenex Implicits fresh fresh_seq.

(* basic properties required by canonical instances *)
Module Export Props.
Section Props.

Context {T : identType}.
Implicit Types (x : T) (s : seq T).

Lemma unpickle_inj : 
  injective (@unpickle T).
Proof. by case: T=> ? [/= ? []]. Qed.

Lemma decode_inj : 
  injective (decode : nat -> T).
Proof. by apply /mk_total_inj /unpickle_inj. Qed.

Lemma encodeK : 
  cancel encode (decode : nat -> T). 
Proof. by apply /mk_totalK /pickleK. Qed.

Lemma decodeK : 
  cancel decode (encode : T -> nat). 
Proof. by apply/inj_can_sym; [exact/encodeK | exact/decode_inj]. Qed.

Lemma encode0 : 
  encode (ident0 : T) = 0%nat.
Proof. by rewrite /ident0; exact /decodeK. Qed.

Lemma encode1 : 
  encode (ident1 : T) = 1%nat.
Proof. by rewrite /ident1; exact /decodeK. Qed.

End Props.
End Props.

Module Order. 
Section Order. 

Context {T : identType}.
Implicit Types (x : T).

Lemma le0x x : ident0 <=^n x.
Proof. rewrite /le /= /countable.Order.le encode0; exact/leq0n. Qed.

End Order.

Module Export Exports.
Implicit Types (T : identType). 
Canonical bLatticeType T := BLatticeType T (BottomMixin (@Order.le0x T)).
Canonical bDistrLatticeType T := [bDistrLatticeType of T].
Coercion bLatticeType : type >-> Order.BLattice.type.
Coercion bDistrLatticeType : type >-> Order.BDistrLattice.type.
End Exports.

End Order.

Module Export Syntax. 
Notation "'\i0'" := (ident0) : ident_scope.
Notation "'\i1'" := (ident1) : ident_scope.
End Syntax.

Module Export Theory.
Section Theory.

Context {T : identType}.
Implicit Types (x : T) (s : seq T).

Lemma fresh_lt x : 
  x <^n fresh x.
Proof. 
  rewrite /fresh /lt /= /countable.Order.lt decodeK. 
  (* ssrnatlia --- should work here, but it doesn't :( *)
  exact /ltnSn.
Qed.

Lemma fresh_inj : 
  injective (@fresh T).
Proof. by rewrite /fresh=> x y /decode_inj [] /pickle_inj. Qed.

Lemma size_nfresh x n : 
  size (nfresh x n) = n.
Proof. by rewrite /nfresh size_traject. Qed.

Lemma nth_nfresh x n i : 
  i < n -> nth x (nfresh x n) i = iter i fresh x.
Proof. by rewrite /nfresh=> ?; apply /nth_traject. Qed.

Lemma nfresh_head x y n : 
  head x (nfresh y n) = if n == 0 then x else y.
Proof. by case: n=> //=. Qed.

Lemma nfresh_sorted x n : 
  sorted (<%O) (nfresh x n).
Proof. 
  rewrite /nfresh; case: n=> //= n.
  apply /sub_path; last exact/fpath_traject.
  move=> ?? /= /eqP <-; exact/fresh_lt.
Qed.  

Lemma nfreshS x n : 
  nfresh x n.+1 = x :: nfresh (fresh x) n.
Proof. by rewrite /nfresh; exact/trajectS. Qed.

Lemma nfreshSr x n : 
  nfresh x n.+1 = rcons (nfresh x n) (iter n fresh x).
Proof. by rewrite /nfresh; exact/trajectSr. Qed.

Lemma fresh_seq_nil : 
  fresh_seq [::] = (\i1 : T).
Proof. by rewrite /fresh_seq /ident1 //=. Qed.

Lemma fresh_seq0 s : 
  \i0 <^n fresh_seq s.
Proof. 
  rewrite /fresh_seq /ident0 /lt /=.
  by rewrite /countable.Order.lt !decodeK. 
Qed.

Lemma fresh_seq_mem x s : 
  x \in s -> x <^n fresh_seq s.
Proof. 
  rewrite /fresh_seq /ident0 /lt /= /countable.Order.lt !decodeK.
  elim s=> [|y {}s IH]=> //=.
  rewrite max0n in_cons=> /orP [/eqP<-|].
  - rewrite ltEnat /=; apply /leq_ltn_trans; last exact/ltnSn.
    apply /foldl_maxn_leq_init.
  move=> /IH H; apply /leq_trans; first exact/H.
  apply /ssrnat.leP /le_n_S /ssrnat.leP.
  by apply /foldl_maxn_leq /leq0n. 
Qed.

Lemma fresh_seq_nmem s : fresh_seq s \notin s.
Proof. by apply/memPn => x /fresh_seq_mem; rewrite lt_neqAle=> /andP[]. Qed.

Lemma fresh_seq_nfresh x n : 
  0 < n -> fresh_seq (nfresh x n) = iter n fresh x.
Proof. 
  rewrite /fresh_seq foldl_maxn_sorted; last first.
  - rewrite sorted_map; apply /sub_sorted /nfresh_sorted.
    rewrite /lt /= /countable.Order.lt=> {}x y /=; exact /ltW.
  have {2}->: 0%nat = @encode T \i0 by apply/esym/encode0.
  rewrite last_map; case: n=> [|{}n].
  - by rewrite encode0=> /=. 
  by rewrite nfreshSr last_rcons iterS /fresh.
Qed.

End Theory.
End Theory.

End Ident.

Export Ident.Exports.
Export Ident.Order.Exports.
Export Ident.Def.
Export Ident.Props.
Export Ident.Syntax.
Export Ident.Theory.

(* Context {T : identType}. *)
(* Variable (x y : T). *)
(* Check (x <=^n y : bool). *)

Lemma nat_unpickle_tot (n : nat) : (unpickle n : option nat).
Proof. done. Qed.

Lemma nat_unpickle_inj : injective (unpickle : nat -> option nat).
Proof. exact/Some_inj. Qed.

Definition nat_identMixin :=
  @Ident.Mixin nat (Countable.class nat_countType) 
               nat_unpickle_tot nat_unpickle_inj.

Canonical nat_identType :=
  Eval hnf in IdentType nat nat_identMixin.
