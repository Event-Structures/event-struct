From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype choice. 
From RelationAlgebra Require Import monoid.
From eventstruct Require Import utils relalg.

(******************************************************************************)
(* This file provides a theory of (homogeneous) monoids and partial monoids.  *)
(*                                                                            *)
(*       Monoid.m T     == a type of monoid structure over elements           *)
(*                         of type T. Consists of binary associative          *)
(*                         operation and a neutral element (unit).            *) 
(*       Monoid.mType d == a type equipped with canonical monoid structure.   *)
(*                                                                            *)
(*       Monoid.cm T     == a type of commutative monoid structure over       *)
(*                          elements of type T. Inherets from ordinary monoid.*)
(*       Monoid.cmType d == a type equipped with canonical structure of       *)
(*                          commutative monoid.                               *)
(*                                                                            *)
(*       Monoid.pcm d     == a type of commutative monoid structures          *)
(*                           with partial operation over elements of type T.  *)
(*                           Inherits from commutative monoid.                *)
(*                           In addition, contains a orthogonality relation   *)  
(*                           which determines pairs of elements whose         *)
(*                           composition is defined.                          *) 
(*       Monoid.pcmType d == a type equipped with canonical structure of      *)
(*                           partial commutative monoidal structure.          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope monoid_scope.
Delimit Scope monoid_scope with monoid.

Local Open Scope monoid_scope.

Reserved Notation "\0" (at level 0).
Reserved Notation "\u" (at level 0).
Reserved Notation "x \+ y" (at level 40, left associativity).
Reserved Notation "x ⟂ y" (at level 20, no associativity).
Reserved Notation "x :- y" (at level 20, no associativity).

Module Monoid.

Module Monoid.
Section ClassDef. 

Record mixin_of (T : Type) := Mixin {
  zero : T;
  plus : T -> T -> T;
  _    : associative plus;
  _    : left_id  zero plus;
  _    : right_id zero plus;
}.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  mixin : mixin_of T;
}.
Unset Primitive Projections.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') in c.

Definition pack c := @Pack disp T c.

Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.

End ClassDef.

Module Import Exports.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
End Exports.

Module Import Types.
Notation m     := Monoid.class_of.
Notation mType := Monoid.type.
End Types.

Module Import Def.
Section Def.

Context {disp : unit} {M : mType disp}.

Definition zero : M := Monoid.zero (Monoid.class M).
Definition plus : M -> M -> M := Monoid.plus (Monoid.class M).

End Def.
End Def.

Prenex Implicits zero plus.

Module Import Syntax.
Notation "\0" := (zero) : monoid_scope.
Notation "x \+ y" := (plus x y) : monoid_scope.
End Syntax.

Module Export Theory.
Section Theory.

Context {disp : unit} {M : mType disp}.

Lemma plusA (x y z : M) : 
  x \+ y \+ z = x \+ (y \+ z). 
Proof. by case: M x y z => ? [[]]. Qed.

Lemma plus0m (x : M) : 
  \0 \+ x = x. 
Proof. by move: x; case: M=> ? [[]]. Qed.

Lemma plusm0 (x : M) : 
  x \+ \0 = x. 
Proof. by move: x; case: M=> ? [[]]. Qed.

End Theory.
End Theory.

End Monoid.

(* Unfortunately, the following Export does not achive the goal.
 * The notations `Monoid.m` and `Monoid.mType` are undefined 
 * if one imports the `monoid.v` from another file. 
 * Thus we have to resort to some copypaste.
 *)

(* Export Monoid.Types. *)
Notation m     := Monoid.class_of.
Notation mType := Monoid.type.

Export Monoid.Exports.
Export Monoid.Def.
Export Monoid.Syntax.
Export Monoid.Theory.

Module Commutative.
Section ClassDef. 

Record mixin_of (T0 : Type) (b : Monoid.class_of T0)
                (T := Monoid.Pack tt b) := Mixin {
  _  : commutative (plus : T -> T -> T);
}.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base  : Monoid.class_of T;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion base : class_of >-> Monoid.class_of.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') in c.

Definition pack c := @Pack disp T c.

Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.

Definition as_mType := @Monoid.Pack disp cT class.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Monoid.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion as_mType : type >-> Monoid.type.
Canonical as_mType.
End Exports.

Module Import Types.
Notation cm     := Commutative.class_of.
Notation cmType := Commutative.type.
End Types.

Module Export Theory.
Section Theory.

Context {disp : unit} {M : cmType disp}.

Lemma plusC (x y : M) : 
  x \+ y = y \+ x. 
Proof. by case: M x y=> ? [[]] ? /= []. Qed.

End Theory.
End Theory.

End Commutative.

(* Export Commutative.Types. *)
Notation cm     := Commutative.class_of.
Notation cmType := Commutative.type.

Export Commutative.Exports.
Export Commutative.Theory.


Module PartialCommutative.
Section ClassDef. 

Record mixin_of (T0 : Type) (b : Commutative.class_of T0)
                (T := Commutative.Pack tt b) := Mixin {
  orth : rel T;
  _    : orth zero zero;
  _    : forall x y, orth x y = orth y x;
  _    : forall x y, orth x y -> orth x zero;
  _    : forall x y z, orth (plus x y) z = orth x (plus y z);
}.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base  : Commutative.class_of T;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Commutative.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') in c.

Definition pack :=
  fun bE b & phant_id (@Commutative.class disp bE) b =>
  fun m => Pack disp (@Class T b m).

Definition as_mType := @Monoid.Pack disp cT class.
Definition as_cmType := @Commutative.Pack disp cT class.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Commutative.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion as_mType : type >-> Monoid.type.
Coercion as_cmType : type >-> Commutative.type.
Canonical as_mType.
Canonical as_cmType.
End Exports.

Module Import Types.
Notation pcm     := PartialCommutative.class_of.
Notation pcmType := PartialCommutative.type.
End Types.

Module Import Def.
Section Def.

Context {disp : unit} {M : pcmType disp}.

Definition orth : rel M := 
  PartialCommutative.orth (PartialCommutative.class M).

Definition valid : pred M := fun x => orth x zero.

Definition invalid : pred M := fun x => negb (orth x zero).

End Def.
End Def.

Prenex Implicits orth valid.

Module Export Syntax.
Notation "x ⟂ y" := (orth x y) : monoid_scope.
End Syntax.

Module Export Theory.
Section Theory.

Context {disp : unit} {M : pcmType disp}.

Implicit Types (x y z : M).

Lemma orth0 : 
  orth \0 (\0 : M). 
Proof. by case: M=> ? [? []]. Qed.

Lemma valid0 : 
  valid (\0 : M). 
Proof. by case: M=> ? [? []]. Qed.

Lemma orth_sym x y :
  x ⟂ y = y ⟂ x.
Proof. by move: x y; case: M=> ? [? []]. Qed.

Lemma orth_valid x y :
  x ⟂ y -> valid x * valid y.
Proof.
  move=> /[dup]; rewrite {2}orth_sym.
  by move: x y; case: M=> ? [? [??? H ???]] /H + /H.
Qed.

Lemma orthA x y z : 
  (x \+ y) ⟂ z = x ⟂ (y \+ z).
Proof. by move: x y z; case: M=> ? [? []]. Qed.

Lemma orth_valid_plus x y : 
  x ⟂ y = valid (x \+ y). 
Proof. by rewrite /valid -[y in LHS]plusm0 orthA. Qed.

(* TODO: find a nicer way to reconcile `pred` with relation-algebra *)
Lemma invalidE : 
  (invalid : rel.dset M) ≡ !(valid : rel.dset M). 
Proof. by rewrite /invalid. Qed.

Lemma invalid_plus x y : 
  invalid x -> invalid (x \+ y). 
Proof. 
  rewrite /invalid=> /negP; apply contra_notN.
  by rewrite orthA plusm0=> /orth_valid []. 
Qed.

End Theory.
End Theory.

End PartialCommutative.

(* Export PartialCommutative.Types. *)
Notation pcm     := PartialCommutative.class_of.
Notation pcmType := PartialCommutative.type.

Export PartialCommutative.Exports.
Export PartialCommutative.Def.
Export PartialCommutative.Syntax.
Export PartialCommutative.Theory.

Module Absorbing.
Section ClassDef. 

Record mixin_of (T0 : Type) (b : Commutative.class_of T0)
                (T := Commutative.Pack tt b) := Mixin {
  undef    : T;
  is_undef : pred T;
  _    : undef <> zero;
  _    : forall x, plus x undef = undef; 
  _    : forall x, reflect (x = undef) (is_undef x);
}.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base  : Commutative.class_of T;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Commutative.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') in c.

Definition pack :=
  fun bE b & phant_id (@Commutative.class disp bE) b =>
  fun m => Pack disp (@Class T b m).

Definition as_mType  := @Monoid.Pack disp cT class.
Definition as_cmType := @Commutative.Pack disp cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Commutative.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion as_mType : type >-> Monoid.type.
Coercion as_cmType : type >-> Commutative.type.
Canonical as_mType.
Canonical as_cmType.
End Exports.

Module Export Types.
Notation apcm     := Absorbing.class_of.
Notation apcmType := Absorbing.type.
End Types.

Module Export Def.
Section Def.

Context {disp : unit} {M : apcmType disp}.

Definition undef : M := 
  Absorbing.undef 
    (Absorbing.class M).

Definition is_undef : pred M := 
  Absorbing.is_undef 
    (Absorbing.class M).

Definition is_def : pred M := 
  fun x => ~~ is_undef x.

End Def.
End Def.

Prenex Implicits undef is_undef.

Module Export Syntax.
Notation "\u" := undef : monoid_scope.
End Syntax.

Module Export Theory.
Section Theory.

Context {disp : unit} {M : apcmType disp}.

Implicit Types (x y z : M).

Lemma undef0 : \u <> (\0 : M). 
Proof. by case: M=> ? [? []]. Qed.

Lemma plusmU x : x \+ \u = \u. 
Proof. by move: x; case: M=> ? [? []]. Qed.

Lemma plusUm x : \u \+ x = \u. 
Proof. by rewrite plusC plusmU. Qed. 

Lemma is_undefP x : reflect (x = \u) (is_undef x).
Proof. by move: x; case: M=> ? [? []]. Qed.

Lemma is_def0 : is_def (\0 : M). 
Proof. 
  apply /negP=> /is_undefP. 
  by move: undef0=> /[swap] ->. 
Qed.

Lemma is_def_plus00 : is_def (\0 \+ (\0 : M)). 
Proof. by rewrite plus0m; exact is_def0. Qed.

Lemma is_def_plus_sym x y : is_def (x \+ y) = is_def (y \+ x). 
Proof. by rewrite plusC. Qed.
 
Lemma is_def_plus_def x y : is_def (x \+ y) -> is_def x.
Proof.
  case H: (is_def x); move: H=> /is_undefP //.
  by move=> ->; rewrite plusUm=> /is_undefP.
Qed.

Lemma is_def_plus_def0 x y : is_def (x \+ y) -> is_def (x \+ \0).
Proof. rewrite plusm0; exact/is_def_plus_def. Qed.

Lemma is_def_plusA x y z : 
  is_def (x \+ y \+ z) = is_def (x \+ (y \+ z)).
Proof. by rewrite plusA. Qed.

End Theory.
End Theory.

Definition pcmMixin (disp : unit) (M : apcmType disp) := 
  @PartialCommutative.Mixin M (class M)
    (fun x y => is_def (x \+ y))
    is_def_plus00
    is_def_plus_sym
    is_def_plus_def0
    is_def_plusA.

Definition as_pcmType (disp : unit) (M : apcmType disp) := 
  @PartialCommutative.Pack disp M 
    (PartialCommutative.Class (pcmMixin M)). 

Module Export ExportsExtra.
Coercion as_pcmType : type >-> PartialCommutative.type.
Canonical as_pcmType.
End ExportsExtra.

End Absorbing.

(* Export Absorbing.Types. *)
Notation apcm     := Absorbing.class_of.
Notation apcmType := Absorbing.type.

Export Absorbing.Exports.
Export Absorbing.ExportsExtra.
Export Absorbing.Def.
Export Absorbing.Syntax.
Export Absorbing.Theory.


Module Divisible.
Section ClassDef. 

(* TODO: currently we fuse together the decidable `divides` 
 *   relation with the axiom of indivisible unit. 
 *   However, in general, this axiom is independent from `divides` relation. 
 *   We fuse them only for convinience, and we might revisit 
 *   this decision in future.
 *)
Record mixin_of (T0 : Type) (b : PartialCommutative.class_of T0)
                (T := Commutative.Pack tt b) := Mixin {
  dvr  : rel T;
  _    : forall (x y : T), x \+ y = \0 -> x = \0; 
  _    : forall (x y : T), reflect (exists z, x \+ z = y) (dvr x y); 
}.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base  : PartialCommutative.class_of T;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> PartialCommutative.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') in c.

Definition pack :=
  fun bE b & phant_id (@PartialCommutative.class disp bE) b =>
  fun m => Pack disp (@Class T b m).

Definition as_mType := @Monoid.Pack disp cT class.
Definition as_cmType := @Commutative.Pack disp cT class.
Definition as_pcmType := @PartialCommutative.Pack disp cT class.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> PartialCommutative.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion as_mType : type >-> Monoid.type.
Coercion as_cmType : type >-> Commutative.type.
Coercion as_pcmType : type >-> PartialCommutative.type.
Canonical as_mType.
Canonical as_cmType.
Canonical as_pcmType.
End Exports.

Module Export Types.
Notation dpcm     := Divisible.class_of.
Notation dpcmType := Divisible.type.
End Types.

Module Export Def.
Section Def.

Context {disp : unit} {M : dpcmType disp}.

Definition dvr : rel M := 
  Divisible.dvr (Divisible.class M). 

End Def.
End Def.

Prenex Implicits dvr.

Module Export Syntax.
Notation "x :- y" := (dvr x y) : monoid_scope.
End Syntax.

Module Export Theory.
Section Theory.

Context {disp : unit} {M : dpcmType disp}.

Implicit Types (x y z : M).

Lemma indiv0 x y : 
  x \+ y = \0 -> x = \0.
Proof. by move: x y; case: M=> ? [? []]. Qed.

Lemma dvrP x y : 
  reflect (exists z, x \+ z = y) (dvr x y). 
Proof. by move: x y; case: M=> ? [? []]. Qed.

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

Lemma dvr_plus (x1 x2 y1 y2 : M) : 
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

End Divisible.

(* Export Divisible.Types. *)
Notation dpcm     := Divisible.class_of.
Notation dpcmType := Divisible.type.

Export Divisible.Exports.
Export Divisible.Def.
Export Divisible.Syntax.
Export Divisible.Theory.
End Monoid.

(* TODO: do not import `Def`, `Syntax`, and `Theory` modules by default (?) *)

Export Monoid.Monoid.Exports.
Export Monoid.Monoid.Def.
Export Monoid.Monoid.Syntax.
Export Monoid.Monoid.Theory.

Export Monoid.Commutative.Exports.
Export Monoid.Commutative.Theory.

Export Monoid.PartialCommutative.Exports.
Export Monoid.PartialCommutative.Def.
Export Monoid.PartialCommutative.Syntax.
Export Monoid.PartialCommutative.Theory.

Export Monoid.Absorbing.Exports.
Export Monoid.Absorbing.ExportsExtra.
Export Monoid.Absorbing.Def.
Export Monoid.Absorbing.Syntax.
Export Monoid.Absorbing.Theory.

Export Monoid.Divisible.Exports.
Export Monoid.Divisible.Def.
Export Monoid.Divisible.Syntax.
Export Monoid.Divisible.Theory.

