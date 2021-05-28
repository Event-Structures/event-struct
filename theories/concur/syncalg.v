From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice.
From mathcomp Require Import ssrnat ssrint.
From RelationAlgebra Require Import monoid.
From eventstruct Require Import utils inhtype monoid.

(******************************************************************************)
(* This file provides a theory of synchronization algebras.                   *)
(*                                                                            *)
(*                                                                            *)
(*  syncalg L  == a type of synchronization algebra structures                *)
(*                over elements of type L, conventionally called labels       *) 
(*                Synchronization algebra is a partial commutative monoid     *)
(*                augumented with synchronization relation \>>, such that:    *)
(*                  a \>> b := if there exists c, s.t. a \+ c = b             *)
(*                Additionally synchronization algebra should not have no     *)
(*                non-trivial inverse elemets, that is:                       *)
(*                  x \+ y = \0 -> x = \0 && y = \0                           *)
(*                non-trivial inverses.                                       *)
(*                                                                            *)
(*  labType d == a type of labels, i.e. a type equipped with                  *)
(*               canonical synchroniazation algebra.                          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monoid_scope.

Declare Scope syncalg_scope.
Delimit Scope syncalg_scope with syncalg.

Local Open Scope syncalg_scope.

Reserved Notation "x :- y" (at level 25, no associativity).
(* Reserved Notation "x \>> y" (at level 25, no associativity). *)

Module SyncAlgebra. 
Section ClassDef.

Record mixin_of (T0 : Type) (b : Monoid.PartialCommutative.class_of T0)
                (T := Monoid.PartialCommutative.Pack tt b) := Mixin {
  dvr  : rel T;
  _    : forall (x y : T), x \+ y = \0 -> x = \0; 
  _    : forall (x y : T), reflect (exists z, x \+ z = y) (dvr x y); 
}.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base  : Monoid.PartialCommutative.class_of T;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion base : class_of >-> Monoid.PartialCommutative.class_of.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') in c.

Definition pack c := @Pack disp T c.

Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.

Definition as_mType := @Monoid.Monoid.Pack disp cT class.
Definition as_cmType := @Monoid.Commutative.Pack disp cT class.
Definition as_pcmType := @Monoid.PartialCommutative.Pack disp cT class.

End ClassDef. 

Module Export Exports.
Coercion base : class_of >-> Monoid.PartialCommutative.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion as_mType : type >-> Monoid.mType.
Coercion as_cmType : type >-> Monoid.cmType.
Coercion as_pcmType : type >-> Monoid.pcmType.
Canonical as_mType.
Canonical as_cmType.
Canonical as_pcmType.
End Exports.

Module Export Types.
Notation syncalg := SyncAlgebra.class_of.
Notation labType := SyncAlgebra.type.
End Types.

Module Export Def.
Section Def.

Context {disp : unit} {L : labType disp}.

Definition dvr : rel L := 
  SyncAlgebra.dvr (SyncAlgebra.class L). 

End Def.
End Def.

Prenex Implicits dvr.

Module Export Syntax.
Notation "x :- y" := (dvr x y) : syncalg_scope.
End Syntax.

Module Export Theory.
Section Theory.

Context {disp : unit} {L : labType disp}.

Implicit Types (x y z : L).

Lemma indiv0 x y : 
  x \+ y = \0 -> x = \0.
Proof. by move: x y; case: L=> ? [? []]. Qed.

Lemma dvrP x y : 
  reflect (exists z, x \+ z = y) (dvr x y). 
Proof. by move: x y; case: L=> ? [? []]. Qed.

Lemma dvr0 x : 
  x :- \0 -> x = \0. 
Proof. by move /dvrP=> [] ? /indiv0. Qed.

Lemma dvr_invalid x y : 
  x :- y -> invalid x -> invalid y. 
Proof. by move /dvrP=> [] z <-; exact/invalid_plus. Qed.

Lemma dvr_refl x : 
  x :- x.
Proof. by apply /dvrP; exists \0; exact/plusm0. Qed.

Lemma dvr_trans x y z : 
  x :- y -> y :- z -> x :- z.
Proof. 
  move=> /dvrP [] u <-  /dvrP [] v <-.
  by apply /dvrP; exists (u \+ v); rewrite plusA.
Qed.

Lemma dvr_plus (x1 x2 y1 y2 : L) : 
  x1 :- y1 -> x2 :- y2 -> (x1 \+ x2) :- (y1 \+ y2).
Proof. 
  move=> /dvrP [] z1 <- /dvrP [] z2 <-.
  apply /dvrP; exists (z1 \+ z2).
  (* TODO: use some tools to deal with associativity and commutativity, 
   *   e.g. aac_rewrite library 
   *)
  rewrite !plusA.
  rewrite -[z1 \+ (x2 \+ z2)]plusA.  
  rewrite -[z1 \+ x2]plusC.  
  by rewrite !plusA.
Qed.

End Theory.
End Theory.

End SyncAlgebra.

(* Export SyncAlgebra.Types. *)
Notation syncalg := SyncAlgebra.class_of.
Notation labType := SyncAlgebra.type.

Export SyncAlgebra.Exports.
Export SyncAlgebra.Def.
Export SyncAlgebra.Syntax.
Export SyncAlgebra.Theory.

Module SharedMemory.
Section SharedMemory. 

Context {Addr : eqType} {Val : eqType}.

Inductive Lab :=
| Write of Addr & Val
| Read  of Addr & option Val
| Emp
| Bot.

Definition addr : Lab -> option Addr := 
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
    | Read  _ v => v
    | _         => None
    end.

Definition is_read : pred Lab := 
  fun l => if l is (Read _ _) then true else false.

Definition is_write : pred Lab := 
  fun l => if l is (Write _ _) then true else false.

Definition is_emp : pred Lab := 
  fun l => if l is Emp then true else false.

Definition is_bot : pred Lab := 
  fun l => if l is Bot then true else false.

Definition eq_lab : rel Lab :=
  fun l1 l2 => 
    match l1, l2 with
    | Read  x a  , Read  y b     => [&& a == b & x == y]
    | Write x a  , Write y b     => [&& a == b & x == y]
    | Emp        , Emp           => true
    | Bot        , Bot           => true
    | _          , _             => false
    end.

Definition eq_addr : rel Lab := 
  orelpre addr eq_op.

Definition eq_value : rel Lab := 
  orelpre value eq_op.

(* for a lack of a better name the monoidal operation 
 * on labels is called merge *)
Definition merge : Lab -> Lab -> Lab := 
  fun l1 l2 => 
    match l1, l2 with 
    | Write x a, Read  y b
    | Read  y b, Write x a =>
      if [&& (x == y) & (b == None)] then 
        Read x (Some a) 
      else Bot
    | _        , Emp       => l1
    | Emp      , _         => l2
    | _        , _         => Bot
    end.

(* merge divisor relation *)
Definition merge_dvr : Lab -> Lab -> bool := 
  fun l1 l2 => 
    match l1, l2 with
    | Write x a, Read  y b =>
      [&& (x == y) & (b == Some a)]
    | Read x None    , Read y (Some a) =>
      (x == y)
    | Emp, _   => true
    | _  , Bot => true
    | _ , _    => eq_lab l1 l2
    end.

Section Theory. 

Lemma eq_labP : Equality.axiom eq_lab.
Proof.
  move=> l1 l2; case: l1; case: l2=> /= *;
    (try by constructor);
    (try by apply: (iffP andP); move=> [] /eqP-> /eqP->).
Qed.

Lemma neq_U0 : Bot <> Emp.
Proof. done. Qed.

Lemma is_botP l : reflect (l = Bot) (is_bot l).
Proof. by case: l; constructor. Qed.

Lemma merge0l l : merge Emp l = l.
Proof. by case l. Qed.

Lemma mergel0 l : merge l Emp = l.
Proof. by case l. Qed.

Lemma mergeUl l : merge Bot l = Bot.
Proof. by case l. Qed.

Lemma mergelU l : merge l Bot = Bot.
Proof. by case l. Qed.

Lemma merge_inverse0 l1 l2 : 
  merge l1 l2 = Emp -> l1 = Emp.
Proof. rewrite /merge; case: l1; case: l2=> // ????; case: ifP=> //. Qed.

Lemma mergeA : associative merge.
Proof. 
  move=> l1 l2 l3.
  case H1: l1=> *; case H2: l2=> *; case H3: l3=> *;
    rewrite ?merge0l ?mergeUl ?mergel0 ?mergelU /merge //;
    repeat (case: eqP)=> //=; congruence.
Qed.

Lemma mergeC : commutative merge.
Proof. 
  move=> l1 l2.
  case H1: l1=> *; case H2: l2=> *; 
    rewrite ?merge0l ?mergeUl ?mergel0 ?mergelU /merge //.
Qed.

Lemma merge_indiv0 l1 l2 : 
  merge l1 l2 = Emp -> l1 = Emp. 
Proof. rewrite /merge; case: l1; case: l2 => // ????; case: ifP=> //. Qed.

Lemma merge_dvrP l1 l2 : 
  reflect (exists l3, merge l1 l3 = l2) (merge_dvr l1 l2).
Proof. 
  apply /(equivP idP).
  (* TODO: a lot of trivial case analysis --- 
   *   would be nice to have some bruteforce tactic for this *)
  rewrite /merge /merge_dvr; case: l1; last 2 first.
  - by split=> //; exists l2; case: l2. 
  - split; [case: l2|]; try by exists Bot.
    by move=> [l3] <-; rewrite /eq_lab; case: l3. 
  - move=> x a; case: l2=> [y b| y b||]; split=>//; try (by move=> /eq_labP //).
    * by move=> /eq_labP <-; exists Emp.
    * move=> [l3]; case: l3=> // [??|<-]; try case: ifP=> //.
      by rewrite /eq_lab !eq_refl.
    * move=> /andP [] /eqP -> /eqP ->. 
      by exists (Read y None); rewrite !eq_refl /=.
    * move=> [l3]; case: l3=> // z c; case: ifP=> //.
      by move=> ?; case=> -> ->; rewrite !eq_refl. 
    * move=> [l3]; case: l3=> // z c; case: ifP=> //.
    * by move=> ?; exists Bot. 
  move=> x a; case: l2=> [y b| y b||]; split; try (by case: a); last 2 first.
  - by move=> [l3]; case: l3=> // ??; case: ifP=> //.
  - by move=> ?; exists Bot.  
  - move=> [l3]; case: l3=> // ??; case: ifP=> //.
  - case: a=> [a|]; last case: b=> [b|].
    * by move=> /eq_labP [] <- <-; exists Emp.
    * by move=> /eqP <-; exists (Write x b); rewrite !eq_refl.
    by move=> /eq_labP [] <-; exists Emp.
  move=> [l3]; case: l3=> //; last first.
  - by move=> [] <- <-; rewrite /eq_lab !eq_refl; case: a.
  by move=> ??; case: ifP=> // /andP [] /eqP -> /eqP -> [] ->; case: b.
Qed.

End Theory.

(* TODO: shorten declaration of instances (use `phand_id` tricks?) *)

Definition mMixin := 
  @Monoid.Monoid.Mixin Lab Emp merge mergeA merge0l mergel0.
Canonical mType := 
  @Monoid.Monoid.pack Lab tt (Monoid.Monoid.Class mMixin). 

Definition cmMixin := 
  @Monoid.Commutative.Mixin Lab (Monoid.Monoid.class mType) mergeC. 
Canonical cmType := 
  @Monoid.Commutative.pack Lab tt (Monoid.Commutative.Class cmMixin). 

Definition apcmMixin := 
  @Monoid.Absorbing.Mixin Lab (Monoid.Commutative.class cmType) 
  Bot is_bot neq_U0 mergelU is_botP. 
Canonical apcmType := 
  Eval hnf in @Monoid.Absorbing.pack Lab tt _ _ id apcmMixin. 

(* TODO: for some reason, pcm notations do not work 
 *   without the following boilerplate.  *)
Canonical pcmType := Monoid.Absorbing.as_pcmType apcmType.
Coercion to_pcmType (l : Lab) : pcmType := l.

(* Context (l1 l2 : Lab). *)
(* Check (l1 ⟂ l2 : bool). *)

Definition syncalgMixin := 
  @SyncAlgebra.Mixin Lab (Monoid.PartialCommutative.class pcmType) 
  merge_dvr merge_indiv0 merge_dvrP.
Canonical syncalgType := 
  @SyncAlgebra.pack Lab tt (SyncAlgebra.Class syncalgMixin). 

End SharedMemory.
End SharedMemory. 

