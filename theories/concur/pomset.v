From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From mathcomp Require Import eqtype choice order finmap. 
From RelationAlgebra Require Import lattice monoid rel boolean.
From eventstruct Require Import utils.

(******************************************************************************)
(* This file provides a theory of pomsets.                                    *)
(* The hierarchy of pomsets is based mathcomp's porderType.                   *)
(*                                                                            *)
(*     LPoset.eventStruct E L == the type of partially ordered sets over      *) 
(*                               elements of type E labeled by type L.        *)
(*                               LPoset of partial causality order (<=) and   *) 
(*                               labelling function lab.                      *)
(*                               We use the name `eventStruct` to denote the  *)
(*                               lposet structure itself (as opposed to       *)
(*                               `eventType`) and for uniformity with the     *)
(*                               theory of event structures.                  *)
(*         LPoset.eventType L == a type of events with labels of type L,      *)
(*                               i.e. a type equipped with canonical labelled *)
(*                               poset structure instance.                    *)
(*                        lab == labelling function.                          *)
(*                         ca == causality order.                             *)
(*                        sca == strict causality order.                      *)
(*                     x <= y == x preceds y in causality order.              *)
(*                               All conventional order notations are         *)
(*                               defined as well.                             *)
(*                                                                            *)
(*           LPoset.hom E1 E2 == a homomorphism between lposet types E1 and   *)
(*                               E1 and E2, that is a label preserving        *) 
(*                               monotone function.                           *)
(*          LPoset.Hom.id     == identity homomorphism.                       *)
(*          LPoset.Hom.tr f g == composition of homomorphisms (g \o f).       *)
(*                                                                            *)
(* Additionally, this file provides notations for homomorphisms which can     *)
(* be used by importing corresponding module: `Import LPoset.Hom.Syntax`.     *)
(*                   E1 ~> E2 == homomorphism.                                *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.
Import Order.LTheory.

Local Open Scope order_scope.
Local Open Scope ra_terms.

Declare Scope pomset_scope.
Delimit Scope pomset_scope with pomset.

Local Open Scope pomset_scope.

Module LPoset.

Module Export LPoset.
Section ClassDef. 

Record mixin_of (E0 : Type) (eb : Order.POrder.class_of E0)
                (E := Order.POrder.Pack tt eb)
                (L : Type) := Mixin {
  lab : E -> L
}.

Set Primitive Projections.
Record class_of (E : Type) (L : Type) := Class {
  base  : Order.POrder.class_of E;
  mixin : mixin_of base L;
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
Notation LPosetType E L m := (@pack E L _ _ id m).
End Exports.

End LPoset.

Notation eventType := LPoset.type.
Notation eventStruct := LPoset.class_of.

Module Export Def.
Section Def.

Context {L : Type} {E : eventType L}.

(* labeling function *)
Definition lab : E -> L := LPoset.lab (LPoset.class E).

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
Section Hom. 

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

End Hom.

Module Export Exports.
Coercion mixin : class_of >-> mixin_of.
Coercion apply : type >-> Funclass.
End Exports.

Module Export Syntax. 
Notation hom := type.
Notation "E1 ~> E2" := (hom E1 E2) (at level 50) : pomset_scope.
End Syntax. 

Module Export Theory.
Section Theory. 
Context {L : Type} {E1 E2 : eventType L} (f : E1 ~> E2).

Lemma lab_preserv :
  { mono f : e / lab e }.
Proof. by case: f => ? [[]]. Qed.

Lemma monotone :
  { homo f : e1 e2 / e1 <= e2 }.
Proof. by case: f => ? [[]]. Qed.

End Theory.
End Theory.

Section Cat.
Context {L : Type}.

Definition id {E : eventType L} : E ~> E.
  by exists id; do 2 constructor=> //. 
Defined.

Definition tr {E1 E2 E3 : eventType L} : (E1 ~> E2) -> (E2 ~> E3) -> (E1 ~> E3).
  move=> f g; exists (g \o f); do 2 constructor=> /=.
  - by move=> e; rewrite !lab_preserv.
  by move=> e1 e2 /(monotone f) /(monotone g).
Defined.

End Cat.

End Hom.

Module Export Bij.
Section Bij. 

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

End Bij.

Module Export Exports.
Coercion base : class_of >-> Hom.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion apply : type >-> Funclass.
Coercion homType : type >-> Hom.type.
Canonical homType.
End Exports.

Module Export Syntax. 
Notation bij := type.
Notation "E1 ≈> E2" := (bij E1 E2) (at level 50) : pomset_scope.
End Syntax. 

Module Export Theory.
Section Theory. 
Context {L : Type} {E1 E2 : eventType L} (f : E1 ≈> E2).

Lemma event_bij :
  bijective f.
Proof. by case: f => ? [[? []]] g ? ?; exists g. Qed.

End Theory.
End Theory.

Section Cat.
Context {L : Type}.

Definition id {E : eventType L} : E ≈> E.
  by exists id; do 1 constructor=> //; exists id. 
Defined.

Definition tr {E1 E2 E3 : eventType L} : (E1 ≈> E2) -> (E2 ≈> E3) -> (E1 ≈> E3).
  move=> f g; exists (Hom.tr f g); constructor. 
  - by case: (Hom.tr f g). 
  case: f=> [? [? []]]; case: g=> [? [? []]].
  by move=> g ?? h ??; exists (h \o g)=> /=; apply /can_comp.
Defined.

End Cat.

End Bij.

Module Export Emb.
Section Emb. 

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

End Emb.

Module Export Exports.
Coercion base : class_of >-> Hom.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion apply : type >-> Funclass.
Coercion homType : type >-> Hom.type.
Canonical homType.
End Exports.

Module Export Syntax. 
Notation emb := type.
Notation "E1 => E2" := (emb E1 E2) (at level 50) : pomset_scope.
End Syntax. 

Module Export Theory.
Section Theory. 
Context {L : Type} {E1 E2 : eventType L} (f : E1 => E2).

Lemma ord_refl e1 e2 :
  (e1 <= e2) = (f e1 <= f e2).
Proof.
  apply/idP/idP; first exact/(monotone f).
  by case: f=> ? [[? []]] => /= /[apply]. 
Qed.

End Theory.
End Theory.

Section Cat.
Context {L : Type}.

Definition id {E : eventType L} : E => E.
  by exists id; do 1 constructor=> //; exists id. 
Defined.

Definition tr {E1 E2 E3 : eventType L} : (E1 => E2) -> (E2 => E3) -> (E1 => E3).
  move=> f g; exists (Hom.tr f g); constructor. 
  - by case: (Hom.tr f g). 
  by constructor=> e1 e2 /=; do 2 rewrite -(ord_refl).
Defined.

End Cat.

End Emb.

Module Export Iso.
Section Iso. 

Context {L : Type} (E1 E2 : eventType L).
Implicit Types (f : E1 -> E2).

Set Primitive Projections.
Record class_of f := Class {
  base  : Bij.class_of f; 
  mixin : Emb.mixin_of f;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Bij.class_of.

Structure type := Pack { apply ; _ : class_of apply }.

Local Coercion apply : type >-> Funclass.

Variables (cT : type).

Definition class := let: Pack _ c as cT' := cT return class_of (apply cT') in c.
Definition clone f c of phant_id class c := @Pack f c.

(* Definition pack := *)
(*   fun bE b & phant_id (@Order.POrder.class tt bE) b => *)
(*   fun m => Pack (@Class E L b m). *)

Definition homType := Hom.Pack class.
Definition bijType := Bij.Pack class.
Definition embType := Emb.Pack (Emb.Class class (mixin class)).

End Iso.

Module Export Exports.
Coercion base : class_of >-> Bij.class_of.
Coercion mixin : class_of >-> Emb.mixin_of.
Coercion apply : type >-> Funclass.
Coercion homType : type >-> Hom.type.
Coercion bijType : type >-> Bij.type.
Coercion embType : type >-> Emb.type.
Canonical homType.
Canonical bijType.
Canonical embType.
End Exports.

Module Export Syntax. 
Notation iso := type.
Notation "E1 ~= E2" := (iso E1 E2) (at level 50) : pomset_scope.
End Syntax. 

Section Cat.
Context {L : Type}.

Definition id {E : eventType L} : E ~= E.
  by exists Bij.id; constructor=> //; case: Bij.id. 
Defined.

Definition sy {E1 E2 : eventType L} : (E1 ~= E2) -> (E2 ~= E1).
  move=> [] f [[]] [] [] HL HM [] g HK HK' [] HR.
  exists g; repeat constructor.
  - by move=> e; rewrite -{2}[e]HK' !HL.
  - by move=> e1 e2; rewrite -{1}[e1]HK' -{1}[e2]HK'; exact/HR.
  - by exists f.
  move=> e1 e2; rewrite -{2}[e1]HK' -{2}[e2]HK'; exact/HM.
Defined.

Definition tr {E1 E2 E3 : eventType L} : (E1 ~= E2) -> (E2 ~= E3) -> (E1 ~= E3).
  move=> f g; exists (Bij.tr f g); constructor; last move=> /=.
  - by case: (Bij.tr f g).
  have ->: (g \o f = Emb.tr f g) by done.
  by case: (Emb.tr f g)=> ? []. 
Defined.

End Cat.

End Iso.

Notation hom := Hom.type.
Notation bij := Bij.type.
Notation emb := Emb.type.
Notation iso := Iso.type.

End LPoset.

Export LPoset.LPoset.Exports.
Export LPoset.Hom.Exports.
Export LPoset.Def.
Export LPoset.Hom.Theory.

