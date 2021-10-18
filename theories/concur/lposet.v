From RelationAlgebra Require Import lattice monoid rel boolean.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq tuple path.
From mathcomp Require Import eqtype choice order fintype finfun finmap. 
From eventstruct Require Import utils inhtype.

(******************************************************************************)
(* This file provides a theory of labelled partially ordered sets             *)
(* (based on mathcomp's porderType).                                          *)
(*                                                                            *)
(*       lPoset.eventType L == a type of events labelled by labels of type L  *)
(*                             equipped with partial order.                   *)
(*     lFinPoset.evenType L == a finite type of events equipped with labelled *)
(*                             poset structure.                               *)
(*        tPoset.evenType t == a lposet structure over tuple t : n.-tuple L.  *)
(*                             A tuple t is treated as labelled total order.  *)
(*                             Events are ordinals 'I_n, label of event i is  *)
(*                             i-th element of tuple, and order is the        *)
(*                             conventional order on natural numbers.         *)
(*                      lab == labelling function.                            *)
(*                       ca == causality order.                               *)
(*                      sca == strict causality order.                        *)
(*                   x <= y == x preceds y in causality order.                *)
(*                             All conventional order notations are           *)
(*                             defined as well.                               *)
(*                                                                            *)
(* We also provide a hierarchy of morphisms between labelled posets.          *)
(*      lPoset.hom E1 E2 == homomorphism between lposets E1 and E2, that is   *)
(*                          label preserving monotone function.               *)
(*     lPoset.ihom E1 E2 == injective homomorphism between lposets E1 and E2. *)
(*     lPoset.bhom E1 E2 == bijective homomorphism between lposets E1 and E2. *)
(*      lPoset.emb E1 E2 == embedding between lposets E1 and E2, that is      *)
(*                          order-reflecting homomorphism.                    *)
(*      lPoset.iso E1 E2 == isomorphism between lposets E1 and E2, that is    *)
(*                          bijective order-reflecting homomorphism.          *)
(* The following notations for morphisms can be used by importing             *)
(* corresponding module: Import lPoset.Mod.Syntax for Mod                     *)
(* in {Hom, iHom, bHom, Emb, Iso}.                                            *)
(*                   E1 ~> E2 == homomorphism.                                *)
(*                   E1 ≈> E2 == injective homomorphism.                      *)
(*                   E1 ≃> E2 == bijective homomorphism.                      *)
(*                   E1 ~≥ E2 == embedding.                                   *)
(*                   E1 ~= E2 == isomorphism.                                 *)
(* Each module Mod in {Hom, iHom, bHom, Emb, Iso} also defines combinators    *)
(* which can be used to build morphisms compositonally.                       *)
(*          lPoset.Mod.id     == identity morphism.                           *)
(*         lPoset.Mod.inv f   == inverse morphisms (for Iso only).            *)
(*        lPoset.Mod.comp f g == composition of morphisms (g \o f).           *)
(*                                                                            *)
(* In case of finite lposets it is possible to check whether given function   *)
(* has properties of certain morphism and also to check if there exists       *)
(* a morphism of certain king between two lposets.                            *)
(*       lFinPoset.ohom f == Some f' if f is homomorphism None otherwise,     *)
(*                           where f' is computationally equal to f but       *) 
(*                           has type of homomorphism                         *)
(*     lFinPoset.homP p q == reflection lemma to check for existence of       *)
(*                           a homomorphism between p and q.                  *)
(* Similar lemmas are available for ihom, bhom, emb, iso.                     *)
(* Additionally, for a tuple lposet the following lemmas are available.       *)
(*     tPoset.homP p q == there exists injective homomorphism between p and q *)
(*                        iff p is a subsequence of q.                        *)
(*     tPoset.isoP p q == there exists isomorphism between p and q            *)
(*                        iff p is equal to q.                                *)
(*                        Note that for tuple lposet bij/emb/iso collapse.    *)
(*                                                                            *)
(* The following constructions are defined on lposets.                        *)
(*        lPoset.ext f == an extension of labelled poset along the            *)
(*                        homomorphism f : E1 -> E2 with events               *)
(*                        of type E1 and the strict causality order defined   *)
(*                        as follows:                                         *)
(*            e1 < e2 <-> e1 < e2 or f e1 < f e2.                             *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.
Import Order.Theory.

Local Open Scope order_scope.
Local Open Scope ra_terms.

Declare Scope lposet_scope.
Delimit Scope lposet_scope with pomset.

Local Open Scope lposet_scope.

Module lPoset.

Module lPoset.
Section ClassDef. 

Record mixin_of (E0 : Type) (L : Type)
                (eb : Order.POrder.class_of E0)
                (E := Order.POrder.Pack tt eb) := Mixin {
  lab : E -> L
}.

Set Primitive Projections.
Record class_of (E : Type) (L : Type) := Class {
  base  : Order.POrder.class_of E;
  mixin : mixin_of L base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Order.POrder.class_of.

Structure type (L : Type) := Pack { sort; _ : class_of sort L }.

Local Coercion sort : type >-> Sortclass.

Variables (E : Type) (L : Type) (cT : type L).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') L in c.
Definition clone c of phant_id class c := @Pack E c.

Definition pack :=
  fun bE b & phant_id (@Order.POrder.class tt bE) b =>
  fun m => Pack (@Class E L b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @Order.POrder.Pack tt cT class.
End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Order.POrder.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> Order.POrder.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Notation lPosetType E L m := (@pack E L _ _ id m).
End Exports.

End lPoset.

Export lPoset.Exports.

Notation eventType := lPoset.type.
Notation eventStruct := lPoset.class_of.

Module Export Def.
Section Def.

Context {L : Type} {E : eventType L}.

(* labeling function *)
Definition lab : E -> L := lPoset.lab (lPoset.class E).

(* causality alias *)
Definition ca : rel E := le.

(* strict causality alias *)
Definition sca : rel E := lt.

Definition ca_closed (X : pred E) : Prop :=
  (* ca · [X] ≦ [X] · ca; *)
  forall x y, x <= y -> X y -> X x.  

End Def.
End Def.

Prenex Implicits lab ca sca.

Module Export Hom.

Module Hom.
Section ClassDef. 

(* TODO: homomorphism between pomsets labelled by different labels? *)
Context {L : Type} (E1 E2 : eventType L).
Implicit Types (f : E1 -> E2).

Record mixin_of f := Mixin {
  _ : forall e, lab (f e) = lab e;
  _ : forall e1 e2, e1 <= e2 -> f e1 <= f e2;
}.

Set Primitive Projections.
Record class_of f := Class {
  mixin : mixin_of f;
}.
Unset Primitive Projections.

Structure type := Pack { apply ; _ : class_of apply }.

Local Coercion apply : type >-> Funclass.

Variables (cT : type).

Definition class := let: Pack _ c as cT' := cT return class_of (apply cT') in c.
Definition clone f c of phant_id class c := @Pack f c.

(* Definition pack := *)
(*   fun bE b & phant_id (@Order.POrder.class tt bE) b => *)
(*   fun m => Pack (@Class E L b m). *)

End ClassDef.

Module Export Exports.
Coercion mixin : class_of >-> mixin_of.
Coercion apply : type >-> Funclass.
End Exports.

End Hom.

Export Hom.Exports.

Module Export Syntax. 
Notation hom := Hom.type.
Notation "E1 ~> E2" := (hom E1 E2) (at level 50) : lposet_scope.
End Syntax. 

Module Export Theory.
Section Theory. 
Context {L : Type} {E1 E2 : eventType L} (f : E1 ~> E2).

(* TODO: rename `lab_preserving`  *)
Lemma lab_preserving :
  { mono f : e / lab e }.
Proof. by case: f => ? [[]]. Qed.

Lemma ca_monotone :
  { homo f : e1 e2 / e1 <= e2 }.
Proof. by case: f => ? [[]]. Qed.

Lemma sca_img e1 e2 : (f e1 < f e2) -> (e1 < e2) || (e1 >< e2).
Proof.
  case H: (e1 < e2)=> //= Hf.
  apply/negP=> /orP [].
  - rewrite le_eqVlt H orbF.
    by move: Hf=> /[swap] /eqP<-; rewrite ltxx.
  move=> /ca_monotone; move: H Hf=> _.
  move: (lt_le_asym (f e1) (f e2))=> /andP H ??. 
  by apply/H.
Qed.

End Theory.
End Theory.

Section Build.
Context {L : Type}.
Implicit Types (E : eventType L).

Lemma id_class {E} : Hom.class_of (id : E -> E).
Proof. done. Qed.

Definition id {E} : E ~> E := Hom.Pack id_class.

Lemma comp_class {E1 E2 E3} (f : E1 ~> E2) (g : E2 ~> E3) : 
  Hom.class_of (g \o f).
Proof. 
  repeat constructor=> /=.
  - by move=> e; rewrite !lab_preserving.
  by move=> e1 e2 /(ca_monotone f) /(ca_monotone g).
Qed.

Definition comp {E1 E2 E3} : (E1 ~> E2) -> (E2 ~> E3) -> (E1 ~> E3) :=
  fun f g => Hom.Pack (comp_class f g).

Lemma of_eqfun_class {E1 E2} (f : E1 ~> E2) g : 
  g =1 f -> Hom.class_of g.
Proof. 
  move=> H; repeat constructor.
  - move=> ?; rewrite !H; exact/lab_preserving.
  move=> ??; rewrite !H; exact/ca_monotone.
Qed.

Definition of_eqfun {E1 E2} (f : E1 ~> E2) g : g =1 f -> E1 ~> E2 := 
  fun eqf => Hom.Pack (of_eqfun_class eqf).

End Build.

End Hom.


Module Export iHom.

Module iHom.
Section ClassDef. 

Context {L : Type} (E1 E2 : eventType L).
Implicit Types (f : E1 -> E2).

Record mixin_of f := Mixin {
  _ : injective f;
}.

Set Primitive Projections.
Record class_of f := Class {
  base  : Hom.class_of f; 
  mixin : mixin_of f;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Hom.class_of.

Structure type := Pack { apply ; _ : class_of apply }.

Local Coercion apply : type >-> Funclass.

Variables (cT : type).

Definition class := let: Pack _ c as cT' := cT return class_of (apply cT') in c.
Definition clone f c of phant_id class c := @Pack f c.

(* Definition pack := *)
(*   fun bE b & phant_id (@Order.POrder.class tt bE) b => *)
(*   fun m => Pack (@Class E L b m). *)

Definition homType := Hom.Pack class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Hom.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion apply : type >-> Funclass.
Coercion homType : type >-> Hom.type.
Canonical homType.
End Exports.

End iHom.

Export iHom.Exports.

Module Export Syntax. 
Notation ihom := iHom.type.
Notation "E1 ≈> E2" := (ihom E1 E2) (at level 50) : lposet_scope.
End Syntax. 

Module Export Theory.
Section Theory. 
Context {L : Type} {E1 E2 : eventType L} (f : E1 ≈> E2).

Lemma ihom_inj : 
  injective f.
Proof. by case: f => ? [[? []]]. Qed.

Lemma sca_monotone :
  { homo f : e1 e2 / e1 < e2 }.
Proof. 
  move=> ?; apply/inj_homo_lt=> //. 
  - exact/ihom_inj. 
  exact/ca_monotone.
Qed.

Lemma ca_img e1 e2 : 
  (f e1 <= f e2) -> (e1 <= e2) || (e1 >< e2).
Proof.
  rewrite le_eqVlt=> /orP[].
  - by move=> /eqP /ihom_inj <-; rewrite lexx.
  move=> /sca_img /orP[|->] //.
  by move=> /ltW ->.
Qed.

End Theory.
End Theory.

Section Build.
Context {L : Type}.
Implicit Types (E : eventType L).

Lemma id_class {E} : iHom.class_of (id : E -> E).
Proof. by repeat constructor=> //. Qed.

Definition id {E} : E ≈> E := iHom.Pack id_class.

Lemma comp_class {E1 E2 E3} (f : E1 ≈> E2) (g : E2 ≈> E3) :
  iHom.class_of (g \o f).
Proof. 
  constructor; first exact/(Hom.comp_class f g).
  by constructor=> x y /= /ihom_inj/ihom_inj.
Qed.

Definition comp {E1 E2 E3} : (E1 ≈> E2) -> (E2 ≈> E3) -> (E1 ≈> E3) := 
  fun f g => iHom.Pack (comp_class f g).

Lemma of_eqfun_class {E1 E2} (f : E1 ≈> E2) g : 
  g =1 f -> iHom.class_of g.
Proof.
  move=> H; constructor; first exact/(Hom.of_eqfun_class H).
  constructor=> /=; apply/eq_inj; first exact/ihom_inj.
  exact/fsym.
Qed.

Definition of_eqfun {E1 E2} (f : E1 ≈> E2) g : g =1 f -> E1 ≈> E2 := 
  fun eqf => iHom.Pack (of_eqfun_class eqf).

End Build.

End iHom.


Module Export bHom.

Module bHom.
Section ClassDef. 

Context {L : Type} (E1 E2 : eventType L).
Implicit Types (f : E1 -> E2).

Record mixin_of f := Mixin {
  g : E2 -> E1;
  _ : cancel f g;
  _ : cancel g f;
}.

Set Primitive Projections.
Record class_of f := Class {
  base  : Hom.class_of f; 
  mixin : mixin_of f;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Hom.class_of.

Structure type := Pack { apply ; _ : class_of apply }.

Local Coercion apply : type >-> Funclass.

Variables (cT : type).

Definition class := let: Pack _ c as cT' := cT return class_of (apply cT') in c.
Definition clone f c of phant_id class c := @Pack f c.

(* Definition pack := *)
(*   fun bE b & phant_id (@Order.POrder.class tt bE) b => *)
(*   fun m => Pack (@Class E L b m). *)

Definition homType := Hom.Pack class.

Lemma ihomMixin : iHom.mixin_of cT.
Proof. 
  constructor; apply/bij_inj.
  by case cT=> [? [? [g]]]; exists g.
Qed.
Definition ihomType := iHom.Pack (iHom.Class class ihomMixin).

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Hom.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion apply : type >-> Funclass.
Coercion homType : type >-> Hom.type.
Coercion ihomType : type >-> iHom.type.
Canonical homType.
Canonical ihomType.
End Exports.

End bHom.

Export bHom.Exports.

Section Def.
Context {L : Type} {E1 E2 : eventType L} (f : bHom.type E1 E2).

Definition invF : E2 -> E1 := bHom.g (bHom.class f).

End Def.

Module Export Syntax. 
Notation bhom := bHom.type.
Notation "E1 ≃> E2" := (bhom E1 E2) (at level 50) : lposet_scope.
End Syntax. 

Module Export Theory.
Section Theory. 
Context {L : Type} {E1 E2 : eventType L} (f : E1 ≃> E2).

Lemma inv_can : 
  cancel f (invF f).
Proof. by case: f => ? [[? []]] ???. Qed.

Lemma can_inv : 
  cancel (invF f) f.
Proof. by case: f => ? [[? []]] ???. Qed.

Lemma bhom_bij :
  bijective f.
Proof. by case: f => ? [[? []]] g ? ?; exists g. Qed.

Lemma inv_lab : 
  { mono (invF f) : e / lab e }.
Proof. by move=> e /=; rewrite -{2}[e]can_inv (lab_preserving f). Qed.

Lemma ca_img_inv e1 e2 : 
  (e1 <= e2) -> (invF f e1 <= invF f e2) || (invF f e1 >< invF f e2).
Proof. by rewrite -{1}[e1]can_inv -{1}[e2]can_inv=> /ca_img. Qed.

Lemma bhom_total : 
  total (<=%O : rel E1) -> total (<=%O : rel E2).
Proof. 
  move=> Ht e1 e2.
  rewrite -[e1]can_inv -[e2]can_inv.
  move: (Ht (invF f e1) (invF f e2)). 
  by move=> /orP[] /(ca_monotone f) ->.
Qed.  

Lemma bhom_ca_reflecting : total (<=%O : rel E1) ->
  { mono f : e1 e2 / e1 <= e2 }.
Proof.
  move=> Ht e1 e2; apply/idP/idP; last exact/(ca_monotone f).
  move=> /ca_img /orP[] //. 
  by rewrite /comparable; move: (Ht e1 e2) ->.
Qed.

End Theory.
End Theory.

Section Build.
Context {L : Type}.
Implicit Types (E : eventType L).

Lemma id_class {E} : bHom.class_of (id : E -> E).
Proof. by constructor=> //; exists id. Qed.

Definition id {E} : E ≃> E := bHom.Pack id_class.

Lemma comp_class {E1 E2 E3} (f : E1 ≃> E2) (g : E2 ≃> E3) :
  bHom.class_of (g \o f).
Proof. 
  constructor; first exact/(Hom.comp_class f g).
  by exists ((invF f) \o (invF g))=> /=; apply/can_comp; 
    try exact/inv_can; try exact/can_inv.
Qed.

Definition comp {E1 E2 E3} : (E1 ≃> E2) -> (E2 ≃> E3) -> (E1 ≃> E3) := 
  fun f g => bHom.Pack (comp_class f g).

Lemma of_eqfun_class {E1 E2} (f : E1 ≃> E2) g : 
  g =1 f -> bHom.class_of g.
Proof.
  move=> H; constructor; first exact/(Hom.of_eqfun_class H).
  exists (invF f)=> ? /=; rewrite !H; [exact/inv_can | exact/can_inv]. 
Qed.

Definition of_eqfun {E1 E2} (f : E1 ≃> E2) g : g =1 f -> E1 ≃> E2 := 
  fun eqf => bHom.Pack (of_eqfun_class eqf).

End Build.

End bHom.


Module Export Emb.

Module Emb.
Section ClassDef. 

Context {L : Type} (E1 E2 : eventType L).
Implicit Types (f : E1 -> E2).

Record mixin_of f := Mixin {
  _ : forall e1 e2, f e1 <= f e2 -> e1 <= e2;
}.

Set Primitive Projections.
Record class_of f := Class {
  base  : Hom.class_of f; 
  mixin : mixin_of f;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Hom.class_of.

Structure type := Pack { apply ; _ : class_of apply }.

Local Coercion apply : type >-> Funclass.

Variables (cT : type).

Definition class := let: Pack _ c as cT' := cT return class_of (apply cT') in c.
Definition clone f c of phant_id class c := @Pack f c.

(* Definition pack := *)
(*   fun bE b & phant_id (@Order.POrder.class tt bE) b => *)
(*   fun m => Pack (@Class E L b m). *)

Definition homType := Hom.Pack class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Hom.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion apply : type >-> Funclass.
Coercion homType : type >-> Hom.type.
Canonical homType.
End Exports.

End Emb.

Export Emb.Exports.

Module Export Syntax. 
Notation emb := Emb.type.
Notation "E1 ~≥ E2" := (emb E1 E2) (at level 50) : lposet_scope.
End Syntax. 

Module Export Theory.
Section Theory. 
Context {L : Type} {E1 E2 : eventType L} (f : E1 ~≥ E2).

Lemma ca_reflecting :
  { mono f : e1 e2 / e1 <= e2 }.
Proof.
  move=> e1 e2; apply/idP/idP; last exact/(ca_monotone f).
  by case: f=> ? [[? []]] => /= /[apply]. 
Qed.

End Theory.
End Theory.

Section Build.
Context {L : Type}.
Implicit Types (E : eventType L).

Lemma id_class {E} : Emb.class_of (id : E -> E).
Proof. by constructor=> //; exists id. Qed.

Definition id {E} : E ~≥ E := Emb.Pack id_class.

Lemma comp_mixin {E1 E2 E3} (f : E1 ~≥ E2) (g : E2 ~≥ E3) : 
  Emb.mixin_of (g \o f).
Proof. by constructor=> ??; rewrite -(ca_reflecting f) -(ca_reflecting g). Qed.

Lemma comp_class {E1 E2 E3} (f : E1 ~≥ E2) (g : E2 ~≥ E3) : 
  Emb.class_of (g \o f).
Proof. 
  constructor; first exact/(Hom.comp_class f g). 
  exact/(comp_mixin f g).
Qed.
  
Definition comp {E1 E2 E3} : (E1 ~≥ E2) -> (E2 ~≥ E3) -> (E1 ~≥ E3) :=
  fun f g => Emb.Pack (comp_class f g).

Lemma of_eqfun_class {E1 E2} (f : E1 ~≥ E2) g :
  g =1 f -> Emb.class_of g.
Proof.
  move=> H; constructor; first exact/(Hom.of_eqfun_class H).
  by constructor=> ??; rewrite !H (ca_reflecting f).
Qed.

Definition of_eqfun {E1 E2} (f : E1 ~≥ E2) g : g =1 f -> E1 ~≥ E2 := 
  fun eqf => Emb.Pack (of_eqfun_class eqf).

End Build.

End Emb.

Module Export Iso.

Module Iso.
Section ClassDef. 

Context {L : Type} (E1 E2 : eventType L).
Implicit Types (f : E1 -> E2).

Set Primitive Projections.
Record class_of f := Class {
  base  : bHom.class_of f; 
  mixin : Emb.mixin_of f;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> bHom.class_of.

Structure type := Pack { apply ; _ : class_of apply }.

Local Coercion apply : type >-> Funclass.

Variables (cT : type).

Definition class := let: Pack _ c as cT' := cT return class_of (apply cT') in c.
Definition clone f c of phant_id class c := @Pack f c.

(* Definition pack := *)
(*   fun bE b & phant_id (@Order.POrder.class tt bE) b => *)
(*   fun m => Pack (@Class E L b m). *)

Definition homType  := Hom.Pack class.
Definition bhomType := bHom.Pack class.
Definition embType  := Emb.Pack (Emb.Class class (mixin class)).

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> bHom.class_of.
Coercion mixin : class_of >-> Emb.mixin_of.
Coercion apply : type >-> Funclass.
Coercion homType  : type >-> Hom.type.
Coercion bhomType : type >-> bHom.type.
Coercion embType  : type >-> Emb.type.
Canonical homType.
Canonical bhomType.
Canonical embType.
End Exports.

End Iso.

Export Iso.Exports.

Module Export Syntax. 
Notation iso := Iso.type.
Notation "E1 ~= E2" := (iso E1 E2) (at level 50) : lposet_scope.
End Syntax. 

Section Build.
Context {L : Type}.
Implicit Types (E : eventType L).

Lemma id_class {E} : Iso.class_of (id : E -> E).
Proof. constructor=> //; exact/bHom.id_class. Qed.

Definition id {E} : E ~= E := Iso.Pack id_class.

Lemma inv_class {E1 E2} (f : E1 ~= E2) :
  Iso.class_of (invF f).
Proof. 
  repeat constructor.
  - by move=> ?; rewrite inv_lab. 
  - move=> e1 e2. 
    rewrite -[e1 in e1 <= e2](can_inv f). 
    rewrite -[e2 in _  <= e2](can_inv f).
    by rewrite (ca_reflecting f).
  - exists f; [exact/can_inv|exact/inv_can].
  move=> e1 e2. 
  rewrite -[e1 in e1 <= e2](can_inv f). 
  rewrite -[e2 in f (invF f e1) <= e2](can_inv f).
  exact/ca_monotone.
Qed.  

Definition inv {E1 E2} : E1 ~= E2 -> E2 ~= E1 := 
  fun f => Iso.Pack (inv_class f).

Lemma comp_class {E1 E2 E3} (f : E1 ~= E2) (g : E2 ~= E3) : 
  Iso.class_of (g \o f).
Proof. 
  constructor; first exact/(bHom.comp_class f g).
  exact/(Emb.comp_mixin f g).
Qed.

Definition comp {E1 E2 E3} : E1 ~= E2 -> E2 ~= E3 -> E1 ~= E3 := 
  fun f g => Iso.Pack (comp_class f g).

Lemma of_eqfun_class {E1 E2} (f : E1 ~= E2) g :
  g =1 f -> Iso.class_of g.
Proof.
  move=> H; constructor; first exact/(bHom.of_eqfun_class H).
  by constructor=> ??; rewrite !H (ca_reflecting f).
Qed.

Definition of_eqfun {E1 E2} (f : E1 ~= E2) g : g =1 f -> E1 ~= E2 := 
  fun eqf => Iso.Pack (of_eqfun_class eqf).

Lemma of_homs_class {E1 E2} (f : E1 ~> E2) (g : E2 ~> E1) : 
  cancel f g -> cancel g f -> Iso.class_of f.
Proof.
  move=> HK HK'; repeat constructor. 
  - exact/(lab_preserving f).
  - exact/(ca_monotone f).
  - by exists g.
  move=> e1 e2. 
  rewrite -[e1 in e1 <= e2]HK.
  rewrite -[e2 in g (f e1) <= e2]HK.
  exact/(ca_monotone g).
  (* We need of_homs_class to be transparent temporarily to prove some lemmas *)
Defined.

Definition of_homs {E1 E2} (f : E1 ~> E2) (g : E2 ~> E1) : 
  cancel f g -> cancel g f -> (E1 ~= E2) := 
    fun HK HK' => Iso.Pack (of_homs_class HK HK').

Lemma of_homs_invE {E1 E2} (f : E1 ~> E2) (g : E2 ~= E1) 
                   (K : cancel f g) (K' : cancel g f) : 
   bHom.invF (of_homs K K') = g.
Proof. done. Qed.

(* Now we can make of_homs_class opaque *)
Global Opaque of_homs_class.

Lemma of_tot_bij_class {E1 E2} (f : E1 ≃> E2) : 
  total (<=%O : rel E1) -> Iso.class_of f.
Proof. 
  move=> Ht; constructor; first exact/(bHom.class f).
  by constructor=> ??; rewrite bhom_ca_reflecting.
Qed.

Definition of_tot_bij {E1 E2 : eventType L} (f : E1 ≃> E2) : 
  total (<=%O : rel E1) -> E1 ~= E2 := 
    fun Ht => Iso.Pack (of_tot_bij_class f Ht).

End Build.

End Iso.

Notation hom := Hom.type.
Notation ihom := iHom.type.
Notation bhom := bHom.type.
Notation emb := Emb.type.
Notation iso := Iso.type.

Module Ext.

Module Order.
Section Order.
Context {L : Type} {E1 E2 : lPoset.eventType L} (f : E1 ~> E2).
Implicit Types (x y : E1).

Definition lt : rel E1 := 
  (<%O : rel E1) ⊔ relpre f (<%O : rel E2).

Definition le : rel E1 := 
  fun x y => (x == y) || (lt x y).

Lemma ltxx x : 
  lt x x = false.
Proof. by rewrite /lt /= !POrderTheory.ltxx. Qed.

Lemma lt_def x y : 
  lt x y = (y != x) && (le x y).
Proof. 
  rewrite /le /lt eq_sym andb_orr andNb /=.
  apply/idP/idP; last by move=> /andP[].
  move=> H; apply /andP; split=> //.
  apply /eqP=> Heq; move: Heq H=> <-. 
  by rewrite !POrderTheory.ltxx.
Qed.

Lemma le_refl :
  reflexive le.
Proof. by move=> x /=; rewrite /le eq_refl. Qed.

Lemma le_anti :
  antisymmetric le.
Proof. 
  rewrite /le=> x y /=.
  move=> /andP [] /orP + /orP.
  move=> []; first by move=> /eqP<-; rewrite ltxx.
  move=> /[swap]; move=> []; first by move=> /eqP<-; rewrite ltxx.
  rewrite /lt /= => /orP + /orP []; move=> [].
  - by move: (lt_asym x y)=> /andP H ??; exfalso; apply/H.
  - move=> /[swap] /ltW /(ca_monotone f).
    move: (le_lt_asym (f x) (f y)).
    by move=> /andP H ??; exfalso; apply/H.
  - move=> /ltW /(ca_monotone f).
    move: (le_lt_asym (f y) (f x)).
    by move=> /andP H ??; exfalso; apply/H.
  by move: (lt_asym (f y) (f x))=> /andP H ??; exfalso; apply/H.
Qed.

Lemma le_trans : 
  transitive le.
Proof. 
  rewrite /le /lt /= => z x y.
  move=> /orP[]; first by move=> /eqP->.
  move=> + /orP[].
  - by move=> /[swap] /eqP-> ->.
  move=> /orP + /orP []; move=> [].
  - by move=> /lt_trans /[apply] ->.
  - move=> /[swap] /ltW /(ca_monotone f). 
    rewrite le_eqVlt=> /orP[]; first by move=> /eqP-> ->.
    by move=> /[swap] /lt_trans /[apply] ->.
  - move=> /ltW /(ca_monotone f). 
    rewrite le_eqVlt=> /orP[]; first by move=> /eqP-> ->.
    by move=> /lt_trans /[apply] ->.
  by move=> /lt_trans /[apply] ->. 
Qed.

Lemma le_id_mono x y :
  x <= y -> le x y.
Proof.  by rewrite /le /lt le_eqVlt orbA /= => ->. Qed.

Lemma le_mono x y :
  le x y -> f x <= f y.
Proof.  
  rewrite /le /lt /= => /orP[]; last move=> /orP[]. 
  - move=> /eqP<-; exact/lexx.
  - by move=> /ltW /(ca_monotone f).
  exact/ltW.
Qed.

Lemma lt_rmono x y :
  f x < f y -> lt x y.
Proof. by rewrite /lt /= => ->. Qed.

Definition porderMixin := 
  @LePOrderMixin E1 le lt lt_def le_refl le_anti le_trans.

Definition porderType := 
  POrderType tt E1 porderMixin.

Definition lposetMixin := 
  lPoset.Mixin (lab : porderType -> L). 

Definition lposetType := 
  lPoset.Pack (@lPoset.Class E1 L (POrder.class porderType) lposetMixin).

End Order.
End Order.

Module Export Def.
Section Def. 
Context {L : Type} {E1 E2 : lPoset.eventType L} (f : E1 ~> E2).

(* TODO: try alternative design with lPoset instance for ext
 *   being parametrized by `f` and give rise to type `E1^f`,
 *   and also define corresponding notations `e1 <=[f] e2`.
 *)
Definition ext : lPoset.eventType L := Order.lposetType f.

End Def.
End Def.

Module Export Theory.
Section Theory.
Context {L : Type} {E1 E2 : lPoset.eventType L}.
Implicit Types (f : E1 ~> E2).

Lemma ext_lt_rmono f (e1 e2 : ext f) :
  f e1 < f e2 -> e1 < e2.
Proof. exact/Order.lt_rmono. Qed.

Lemma ext_le_rmono (f : E1 ≃> E2) (e1 e2 : ext f) :
  f e1 <= f e2 -> e1 <= e2.
Proof. 
  rewrite !le_eqVlt=> /orP[]. 
  - by move=> /eqP /(bij_inj (bhom_bij f)) /eqP->. 
  by move=> /ext_lt_rmono ->.
Qed.

Lemma ext_incomp f (e1 e2 : ext f) :
  e1 >< e2 -> (f e1 == f e2) || (f e1 >< f e2).
Proof. 
  case H: (f e1 <= f e2); move: H.
  - rewrite le_eqVlt=> /orP[/eqP->|]; rewrite ?eq_refl=> //.
    by rewrite {1}/comparable=> /ext_lt_rmono /ltW ->.
  case H: (f e2 <= f e1); move: H.
  - rewrite le_eqVlt=> /orP[/eqP->|]; rewrite ?eq_refl=> //.
    by rewrite /comparable=> /ext_lt_rmono /ltW ->; rewrite orbT. 
  by rewrite {2}/comparable=> -> ->.
Qed.

End Theory.
End Theory.

Section Build.
Context {L : Type} {E1 E2 : lPoset.eventType L}.
Implicit Types (f : E1 ~> E2).
Implicit Types (g : E1 ≃> E2).

Lemma bhom_class f : bHom.class_of (id : E1 -> ext f).
Proof. 
  repeat constructor. 
  - exact/Order.le_id_mono.
  by exists (id : ext f -> E1).
Qed.

Definition bhom f : E1 ≃> ext f := 
  bHom.Pack (bhom_class f).

Lemma hom_class f : Hom.class_of (f : ext f -> E2).
Proof. 
  repeat constructor.
  - exact/(lab_preserving f).
  move=> e1 e2; exact/Order.le_mono.
Qed.  

Definition hom f : ext f ~> E2 := 
  Hom.Pack (hom_class f).

Lemma iso_class g : Iso.class_of (g : ext g -> E2).
Proof. 
  constructor; constructor. 
  - exact/(hom_class g).
  - exists ((bhom g) \o (bHom.invF g))=> ? /=; 
      [exact/inv_can | exact/can_inv].
  exact/ext_le_rmono.
Qed.

Definition iso (g : E1 ≃> E2) : ext g ~= E2 := 
  Iso.Pack (iso_class g).

End Build.

End Ext.

Notation ext := (Ext.Def.ext).

Module Syntax. 
Export Hom.Syntax.
Export iHom.Syntax.
Export bHom.Syntax.
Export Emb.Syntax.
Export Iso.Syntax.
End Syntax.

End lPoset.

Export lPoset.lPoset.Exports.
Export lPoset.Def.

Export lPoset.Hom.Hom.Exports.
Export lPoset.iHom.iHom.Exports.
Export lPoset.bHom.bHom.Exports.
Export lPoset.Emb.Emb.Exports.
Export lPoset.Iso.Iso.Exports.

Export lPoset.Hom.Theory.
Export lPoset.iHom.Theory.
Export lPoset.bHom.Theory.
Export lPoset.Emb.Theory.

Export lPoset.Ext.Theory.

Notation lposet := (lPoset.eventStruct).


Module lLoset.

Module Export lLoset.
Section ClassDef. 

Set Primitive Projections.
Record class_of (E : Type) (L : Type) := Class { 
  base  : Order.Total.class_of E;
  mixin : lPoset.lPoset.mixin_of L base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Order.Total.class_of.

Structure type (L : Type) := Pack { sort; _ : class_of sort L }.

Local Coercion sort : type >-> Sortclass.

Variables (E : Type) (L : Type) (cT : type L).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') L in c.
Definition clone c of phant_id class c := @Pack E c.

Definition pack :=
  fun bE b & phant_id (@lPoset.lPoset.class L bE) b =>
  fun m => Pack (@Class E L b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @Order.POrder.Pack tt cT class.
Definition latticeType := @Lattice.Pack tt cT class.
Definition distrLatticeType := @DistrLattice.Pack tt cT class.
Definition orderType := @Order.Total.Pack tt cT class.
Definition lposetType := 
  @lPoset.lPoset.Pack L cT (lPoset.lPoset.Class (mixin class)).
End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Order.Total.class_of.
Coercion mixin : class_of >-> lPoset.lPoset.mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> Order.POrder.type.
Coercion latticeType : type >-> Lattice.type.
Coercion distrLatticeType : type >-> DistrLattice.type.
Coercion orderType : type >-> Order.Total.type.
Coercion lposetType : type >-> lPoset.lPoset.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical latticeType.
Canonical distrLatticeType.
Canonical orderType.
Canonical lposetType.
Notation lLosetType E L m := (@pack E L _ _ id m).
End Exports.

End lLoset.

Notation eventType := lLoset.type.
Notation eventStruct := lLoset.class_of.

Import lPoset.Hom.Syntax.
Import lPoset.bHom.Syntax.
Import lPoset.Emb.Syntax.
Import lPoset.Iso.Syntax.

End lLoset.

Export lLoset.lLoset.Exports.


Module lFinPoset.

Module lFinPoset.
Section ClassDef. 

Set Primitive Projections.
Record class_of (E : Type) (L : Type) := Class { 
  base  : Order.FinPOrder.class_of E;
  mixin : lPoset.lPoset.mixin_of L base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Order.FinPOrder.class_of.

Structure type (L : Type) := Pack { sort; _ : class_of sort L }.

Local Coercion sort : type >-> Sortclass.

Variables (E : Type) (L : Type) (cT : type L).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') L in c.
Definition clone c of phant_id class c := @Pack E c.

Definition pack :=
  fun bE b & phant_id (@Order.FinPOrder.class bE) b =>
  fun m => Pack (@Class E L b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition countType := @Countable.Pack cT class.
Definition finType := @Finite.Pack cT class.
Definition porderType := @Order.POrder.Pack tt cT class.
Definition finPOrderType := @Order.FinPOrder.Pack tt cT class.
Definition lposetType := 
  @lPoset.lPoset.Pack L cT (lPoset.lPoset.Class (mixin class)).
End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Order.FinPOrder.class_of.
Coercion mixin : class_of >-> lPoset.lPoset.mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Coercion finType : type >-> Finite.type.
Coercion porderType : type >-> Order.POrder.type.
Coercion finPOrderType : type >-> Order.FinPOrder.type.
Coercion lposetType : type >-> lPoset.lPoset.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical finPOrderType.
Canonical lposetType.
Notation lFinPosetType E L m := (@pack E L _ _ id m).
End Exports.

End lFinPoset.

Export lFinPoset.Exports.

Notation eventType := lFinPoset.type.
Notation eventStruct := lFinPoset.class_of.

Import lPoset.Syntax.

Module Export Theory.
Section Theory.
Context {L : eqType} (E1 E2 : eventType L).
Implicit Types (f : E1 -> E2).

Lemma fin_lab_preservingP f : 
  reflect { mono f : e / lab e } [forall e, lab (f e) == lab e].
Proof. apply/forallPP=> ?; exact/eqP. Qed.

Lemma fin_ca_monotoneP f : 
  reflect { homo f : e1 e2 / e1 <= e2 } 
          [forall e1, forall e2, (e1 <= e2) ==> (f e1 <= f e2)].
Proof. repeat apply/forallPP=> ?; exact/implyP. Qed.

Lemma fin_ca_reflectingP f : 
  reflect { mono f : e1 e2 / e1 <= e2 } 
          [forall e1, forall e2, (e1 <= e2) == (f e1 <= f e2)].
Proof. repeat apply/forallPP=> ?; rewrite eq_sym; exact/eqP. Qed.

End Theory.
End Theory.

Module Export Hom.
Section Hom.
Context {L : eqType} (E1 E2 : eventType L).

Definition hom_pred (f : {ffun E1 -> E2}) := 
  [&& [forall e, lab (f e) == lab e]  
    & [forall e1, forall e2, (e1 <= e2) ==> (f e1 <= f e2)]
  ].

(* TODO: try to shorten copy-paste in hom definitions, 
 *   try to generalize to arbitary pair of P and p, 
 *   s.t. reflect P p  
 *)

(* TODO: try alternative notations: 
 *   {hom E1 -> E2} for homomorphism
 *   {fhom E1 -> E2} for finite homomorphism
 *)

Lemma fhom_lab_preserving (f : {ffun E1 -> E2 | hom_pred}) :
  [forall e, lab (f e) == lab e].
Proof. by case: f=> [{}f] /= /andP[]. Qed.

Lemma fhom_ca_monotone (f : {ffun E1 -> E2 | hom_pred}) :
  [forall e1, forall e2, (e1 <= e2) ==> (f e1 <= f e2)].
Proof. by case: f=> [{}f] /= /andP[]. Qed.

Lemma hom_pred_of_hom (f : E1 ~> E2) : 
  hom_pred [ffun x => f x].
Proof. 
  apply/andP; split.
  - apply/forallP=> e; rewrite ffunE /=. 
    by apply/eqP/(lab_preserving f).
  apply/forallP=> e1; apply/forallP=> e2.
  apply/implyP; rewrite !ffunE /=.
  by apply/(ca_monotone f).
Qed.

Definition fhom_of_hom : (E1 ~> E2) -> {ffun E1 -> E2 | hom_pred} := 
  fun (f : E1 ~> E2) => Sub [ffun x => f x] (hom_pred_of_hom f).

Lemma hom_mixin (f : {ffun E1 -> E2 | hom_pred}) : 
  lPoset.Hom.Hom.mixin_of f.
Proof.
  constructor.
  - apply/fin_lab_preservingP/fhom_lab_preserving.
  apply/fin_ca_monotoneP/fhom_ca_monotone.
Qed.

Definition hom_of_fhom : {ffun E1 -> E2 | hom_pred} -> (E1 ~> E2) :=
  fun f => lPoset.Hom.Hom.Pack (lPoset.Hom.Hom.Class (hom_mixin f)).

Definition ohom f : option (E1 ~> E2) := 
  omap hom_of_fhom (insub [ffun x => f x]).

Lemma homP :
  reflect ?|E1 ~> E2| ??|{ffun E1 -> E2 | hom_pred}|.
Proof.
  apply/equivP; first exact/fin_inhP.
  apply/(inh_iff hom_of_fhom).  
  exact/fhom_of_hom.
Qed.

End Hom.

Prenex Implicits hom_pred hom_of_fhom fhom_of_hom ohom.

End Hom.

Module Export iHom.
Section iHom.
Context {L : eqType} (E1 E2 : eventType L).

Definition ihom_pred (f : {ffun E1 -> E2}) := 
  hom_pred f && injectiveb f.

Lemma fihom_inj (f : {ffun E1 -> E2 | ihom_pred}) :
  injective f.
Proof. by case: f=> [{}f] /= /andP[] ? /injectiveP. Qed.

Lemma ihom_pred_of_ihom (f : E1 ≈> E2) : 
  ihom_pred [ffun x => f x].
Proof. 
  apply/andP; split; first exact/hom_pred_of_hom.
  apply/injectiveP=> x y; rewrite !ffunE; exact/ihom_inj.
Qed.

Definition fhom_of_fihom (f : {ffun E1 -> E2 | ihom_pred}) : 
  {ffun E1 -> E2 | hom_pred} := Sub _ (proj1 (andP (valP f))).

Definition fihom_of_ihom (f : E1 ≈> E2) : {ffun E1 -> E2 | ihom_pred} := 
  Sub [ffun x => f x] (ihom_pred_of_ihom f).

Lemma ihom_mixin (f : {ffun E1 -> E2 | ihom_pred}) : 
  lPoset.iHom.iHom.mixin_of f.
Proof. constructor; exact/fihom_inj. Qed.

Definition ihom_of_fihom (f : {ffun E1 -> E2 | ihom_pred}) : (E1 ≈> E2) :=
  let base  := lPoset.Hom.Hom.class (hom_of_fhom (fhom_of_fihom f)) in
  let mixin := ihom_mixin f in 
  lPoset.iHom.iHom.Pack (lPoset.iHom.iHom.Class base mixin).

Definition oihom f : option (E1 ≈> E2) := 
  omap ihom_of_fihom (insub [ffun x => f x]).

Lemma ihomP :
  reflect ?|E1 ≈> E2| ??|{ffun E1 -> E2 | ihom_pred}|.
Proof.
  apply/equivP; first exact/fin_inhP.
  apply/(inh_iff ihom_of_fihom).  
  exact/fihom_of_ihom.
Qed.

End iHom.

Prenex Implicits ihom_pred ihom_of_fihom fihom_of_ihom oihom.

End iHom.

Module Export bHom.
Section bHom.
Context {L : eqType} (E1 E2 : eventType L).

Definition bhom_pred (f : {ffun E1 -> E2}) := 
  ihom_pred f && (#|E2| <= #|E1|).

Lemma fbhom_bij (f : {ffun E1 -> E2 | bhom_pred}) :
  bijective f.
Proof. 
  case: f=> [{}f] /= /andP[] /andP[] ?.
  move=> /injectiveP; exact/inj_card_bij.  
Qed.

Lemma bhom_pred_of_bhom (f : E1 ≃> E2) : 
  bhom_pred [ffun x => f x].
Proof. 
  apply/andP; split; first exact/ihom_pred_of_ihom.
  by apply/eq_leq/esym/bij_eq_card/(bhom_bij f).
Qed.

Definition fihom_of_fbhom (f : {ffun E1 -> E2 | bhom_pred}) : 
  {ffun E1 -> E2 | ihom_pred} := Sub _ (proj1 (andP (valP f))).

Definition fbhom_of_bhom (f : E1 ≃> E2) : {ffun E1 -> E2 | bhom_pred} := 
  Sub [ffun x => f x] (bhom_pred_of_bhom f).

Lemma bhom_mixin (f : {ffun E1 -> E2 | bhom_pred}) : 
  lPoset.bHom.bHom.mixin_of f.
Proof. 
  move: (valP f)=> /andP[] /andP[] ? /injectiveP Hi Hn.
  pose g := (fun y => iinv (inj_card_onto Hi Hn y)).
  by exists g=> y; rewrite /g ?iinv_f ?f_iinv.
Qed.

Definition bhom_of_fbhom (f : {ffun E1 -> E2 | bhom_pred}) : (E1 ≃> E2) :=
  let fihom := fihom_of_fbhom f in
  let base  := lPoset.Hom.Hom.class (hom_of_fhom (fhom_of_fihom fihom)) in
  let mixin := bhom_mixin f in 
  lPoset.bHom.bHom.Pack (lPoset.bHom.bHom.Class base mixin).

Definition obhom f : option (E1 ≃> E2) := 
  omap bhom_of_fbhom (insub [ffun x => f x]).

Lemma bhomP :
  reflect ?|E1 ≃> E2| ??|{ffun E1 -> E2 | bhom_pred}|.
Proof.
  apply/equivP; first exact/fin_inhP.
  apply/(inh_iff bhom_of_fbhom).  
  exact/fbhom_of_bhom.
Qed.

End bHom.

Prenex Implicits bhom_pred bhom_of_fbhom fbhom_of_bhom obhom.

End bHom.

Module Export Emb.
Section Emb.
Context {L : eqType} (E1 E2 : eventType L).

Definition emb_pred (f : {ffun E1 -> E2}) := 
  hom_pred f && [forall e1, forall e2, (f e1 <= f e2) ==> (e1 <= e2)].

Lemma femb_ca_reflecting (f : {ffun E1 -> E2 | emb_pred}) :
  [forall e1, forall e2, (e1 <= e2) == (f e1 <= f e2)].
Proof. 
  case: f=> [{}f] /= /andP[] /andP[] ?.
  move=> /forall2P H1 /forall2P H2.
  apply/forall2P=> e1 e2; apply/eqP/eq_bool_iff.
  split; apply/implyP; [exact/H1 | exact/H2].
Qed.

Lemma emb_pred_of_emb (f : E1 ~≥ E2) : 
  emb_pred [ffun x => f x].
Proof. 
  apply/andP; split; first exact/hom_pred_of_hom. 
  apply/forall2P=> e1 e2; rewrite !ffunE.
  by apply/implyP; rewrite (ca_reflecting f).
Qed.

Lemma emb_mixin (f : {ffun E1 -> E2 | emb_pred}) : 
  lPoset.Emb.Emb.mixin_of f.
Proof. 
  constructor=> e1 e2.
  move: (femb_ca_reflecting f).
  move=> /fin_ca_reflectingP H. 
  by move: (H e1 e2)=> ->.
Qed.

Definition fhom_of_femb (f : {ffun E1 -> E2 | emb_pred}) : 
  {ffun E1 -> E2 | hom_pred} := Sub _ (proj1 (andP (valP f))).

Definition femb_of_emb (f : E1 ~≥ E2) : {ffun E1 -> E2 | emb_pred} := 
  Sub [ffun x => f x] (emb_pred_of_emb f).

Definition emb_of_femb (f : {ffun E1 -> E2 | emb_pred}) : (E1 ~≥ E2) :=
  let base  := lPoset.Hom.Hom.class (hom_of_fhom (fhom_of_femb f)) in
  let mixin := emb_mixin f in 
  lPoset.Emb.Emb.Pack (lPoset.Emb.Emb.Class base mixin).

Definition oemb f : option (E1 ~≥ E2) := 
  omap emb_of_femb (insub [ffun x => f x]).

Lemma embP :
  reflect ?|E1 ~≥ E2| ??|{ffun E1 -> E2 | emb_pred}|.
Proof.
  apply/equivP; first exact/fin_inhP.
  apply/(inh_iff emb_of_femb).  
  exact/femb_of_emb.
Qed.

End Emb.

Prenex Implicits emb_pred emb_of_femb femb_of_emb oemb.

End Emb.

Module Export Iso.
Section Iso.
Context {L : eqType} (E1 E2 : eventType L).

Definition iso_pred (f : {ffun E1 -> E2}) := 
  bhom_pred f && [forall e1, forall e2, (f e1 <= f e2) ==> (e1 <= e2)].

Lemma iso_pred_of_iso (f : E1 ~= E2) : 
  iso_pred [ffun x => f x].
Proof. 
  apply/andP; split; first exact/bhom_pred_of_bhom. 
  apply/forall2P=> e1 e2; rewrite !ffunE. 
  rewrite (ca_reflecting f); exact/implyP.
Qed.

Lemma emb_pred_of_fiso f : iso_pred f -> emb_pred f. 
Proof. by move=> /andP[] /andP[] /andP[] Hf _ _ Hm; apply/andP. Qed. 

Definition fbhom_of_fiso (f : {ffun E1 -> E2 | iso_pred}) : 
  {ffun E1 -> E2 | bhom_pred} := Sub _ (proj1 (andP (valP f))).

Definition femb_of_fiso (f : {ffun E1 -> E2 | iso_pred}) : 
  {ffun E1 -> E2 | emb_pred} := Sub _ (emb_pred_of_fiso (valP f)).

Definition fiso_of_iso (f : E1 ~= E2) : {ffun E1 -> E2 | iso_pred} := 
  Sub [ffun x => f x] (iso_pred_of_iso f).

Definition iso_of_fiso (f : {ffun E1 -> E2 | iso_pred}) : (E1 ~= E2) :=
  let fbhom := fbhom_of_fiso f in
  let base  := lPoset.bHom.bHom.class (bhom_of_fbhom fbhom) in
  let mixin := emb_mixin (femb_of_fiso f) in 
  lPoset.Iso.Iso.Pack (lPoset.Iso.Iso.Class base mixin).

Definition oiso f : option (E1 ~= E2) := 
  omap iso_of_fiso (insub [ffun x => f x]).

Lemma isoP :
  reflect ?|E1 ~= E2| ??|{ffun E1 -> E2 | iso_pred}|.
Proof.
  apply/equivP; first exact/fin_inhP.
  apply/(inh_iff iso_of_fiso).  
  exact/fiso_of_iso.
Qed.

End Iso.

Prenex Implicits iso_pred iso_of_fiso fiso_of_iso oiso.

End Iso.

End lFinPoset.

Export lFinPoset.lFinPoset.Exports.
Export lFinPoset.Theory.


Module tPoset.

Module tPoset.
Section tPoset.

Import Order.OrdinalOrder.Exports.

Context {L : Type} {n : nat} (t : n.-tuple L).

Definition tsca : rel 'I_n := (<%O : rel 'I_n).

Definition tca : rel 'I_n := (<=%O : rel 'I_n).

Definition tlab : 'I_n -> L := tnth t.

Definition lposetMixin := 
  @lPoset.lPoset.Mixin 'I_n L 
    (Order.FinPOrder.class (OrdinalOrder.finPOrderType n)) tlab. 
Canonical lposetType := 
  lPoset.lPoset.Pack (lPoset.lPoset.Class lposetMixin).

(* For some reasons, `finOrderType` requires non-emptiness.
 * Because of this restriction in order.v hierarchy 
 * we cannot utilize here the order type which is both finite and total, 
 * (since we don't want to enforce non-emptiness of tuples/words). 
 * Therefore, until this issue won't be solved in mathcomp, 
 * we have to stick to only one branch of the hierarchy. 
 * Choosing `finPOrderType` looks more pragmatic, 
 * since then we can just state a lemma that the 
 * causality order on tuples/words is total and work with that. 
 * Once the issue is resolved, we can rework this and move 
 * part of the theory into more generic setting of lLoset types. 
 *)

(* Canonical llosetType := *)
(*   lLoset.lLoset.Pack (lLoset.lLoset.Class lposetMixin). *)

Canonical lfinposetType := 
  lFinPoset.lFinPoset.Pack (lFinPoset.lFinPoset.Class lposetMixin).

Lemma tltE : (lt : rel lfinposetType) = (<%O : rel nat).
Proof. by []. Qed.

Lemma tscaE : (sca : rel lfinposetType) = (<%O : rel nat).
Proof. by []. Qed.

Lemma tleE : (le : rel lfinposetType) = (<=%O : rel nat).
Proof. by []. Qed.

Lemma tcaE : (ca : rel lfinposetType) = (<=%O : rel nat).
Proof. by []. Qed.

Lemma tlabE : (lab : lfinposetType -> L) = (tnth t).
Proof. by []. Qed.

End tPoset.

Module Export Exports.
Canonical lposetType.
(* Canonical llosetType. *)
Canonical lfinposetType.

Definition tltE := @tltE.
Definition tscaE := @tscaE.
Definition tleE := @tleE.
Definition tcaE := @tcaE.
Definition tlabE := @tlabE.
End Exports.

End tPoset.

Export tPoset.Exports.

Notation eventType := tPoset.lfinposetType.

Import lPoset.Syntax.

Module Export Theory.
Section Theory. 
Context {L : Type} {n : nat} (t : n.-tuple L).
Implicit Types (e : eventType t).

Lemma event_ltn e :
  (e < n)%N.
Proof. by move: (valP e). Qed.

Lemma tca_total : total (ca : rel (eventType t)).
Proof. rewrite tcaE; exact/leq_total. Qed.

End Theory.
End Theory.


Module Iso.

Section Def.
Context {L : eqType} {n m : nat} (t : n.-tuple L) (u : m.-tuple L).

Definition of_bij : 
  (eventType t ≃> eventType u) -> (eventType t ~≥ eventType u) := 
    fun f => lPoset.Iso.of_tot_bij f (@tca_total L n t).

End Def.

End Iso. 

Section HomP. 
Context {L : eqType} {n m : nat} (t : n.-tuple L) (u : m.-tuple L).

Lemma homP : 
  reflect ?|eventType t ≈> eventType u| (subseq t u).
Proof. 
  apply/(iffP idP); last first.
  - move=> [f]; apply/subseqP.
    pose g := sub_lift (fun i => (m + i)%N) (fun i => val (f i)) : nat -> nat.  
    pose s := mkseq g n.
    exists (mkmask s m).
    + rewrite size_mkmask ?size_nseq ?size_tuple // all_map /=.
      subst g=> /=; apply/allP=> i /=.
      rewrite mem_iota addnC addn0=> /andP[??]. 
      by rewrite sub_liftT.
    apply/esym; subst s. 
    rewrite (@mkmask_mask L _ _ t)=> //.
    + by move=> ???; apply (sca_monotone f).
    + exact/ihom_inj.
    by move=> ?; rewrite -tlabE -tlabE lab_preserving.
  move: m u; clear m u.
  case=> [u|m u].
  - move: (tuple0 u)=> /= -> /=.
    rewrite -size_eq0 size_tuple=> /eqP Hn.
    have efalse: (forall e : eventType t, False).
    + by rewrite /eventType /= Hn => [[i]]; rewrite ltn0. 
    have f: (eventType t ~> eventType ([tuple] : 0.-tuple L)).
    + by exists (fun e => match efalse e with end).
    constructor; exists f; repeat constructor; by move=> ?. 
  move=> /subseqP=> [[b Hsz Hb]].
  pose g := (fun => ord_max) : eventType t -> eventType u.
  pose f := sub_down g (find_nth id b).
  pose l := (@lab L (eventType u) ord_max) : L.
  have He: forall (e : eventType t), (find_nth id b e < m.+1)%N.
  - move=> e; rewrite -[m.+1](size_tuple u) -Hsz.
    by rewrite (mask_size_find_nth Hsz) // -Hb (size_tuple t).
  constructor; unshelve eexists; [exact/f |]. 
  repeat constructor; move=>/=.
  - move=> e; rewrite !tlabE. 
    rewrite !(tnth_nth l) Hb (nth_mask l e Hsz).
    by rewrite val_sub_downT //. 
  - move=> e1 e2; rewrite !tleE !val_sub_downT //; exact/find_nth_leq.
  move=> e1 e2=> /=; subst f.
  apply/sub_down_inj_inT; rewrite ?/in_mem //=.
  by move=>?? /find_nth_inj/val_inj. 
Qed.

End HomP.

Section IsoP.
Context {L : eqType} {n m : nat} (t : n.-tuple L) (u : m.-tuple L).

Lemma isoP : 
  reflect ?|eventType t ~= eventType u| (t == u :> seq L).
Proof. 
  apply/(iffP idP); last first.  
  - move=> [f]; move: (lPoset.Iso.inv f)=> g.
    apply/eqP/subseq_anti/andP. 
    split; apply/homP; eexists; [exact/f | exact/g]. 
  move=> /eqP H; have Hn: n = m. 
  - by rewrite -(size_tuple t) -(size_tuple u) H.
  move: u H; clear u; case Hn=> u.
  move=> /val_inj ->.
  constructor; exact/lPoset.Iso.id. 
Qed.

End IsoP. 

End tPoset.

Export tPoset.tPoset.Exports.
Export tPoset.Theory. 

(* Context (L : Type) (n : nat) (t : n.-tuple L). *)
(* Context (e e1 e2 : tPoset.eventType t). *)
(* Check (lab e : L). *)
(* Check (e1 <= e2 : bool). *)
