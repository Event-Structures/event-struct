From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From mathcomp Require Import eqtype choice order finmap. 
From RelationAlgebra Require Import lattice monoid rel boolean.
From eventstruct Require Import utils.

(******************************************************************************)
(* This file provides a theory of pomsets.                                    *)
(* The hierarchy of pomsets is based mathcomp's porderType.                   *)
(*                                                                            *)
(*     lPoset.eventStruct E L == the type of partially ordered sets over      *) 
(*                               elements of type E labeled by type L.        *)
(*                               lPoset of partial causality order (<=) and   *) 
(*                               labelling function lab.                      *)
(*                               We use the name `eventStruct` to denote the  *)
(*                               lposet structure itself (as opposed to       *)
(*                               `eventType`) and for uniformity with the     *)
(*                               theory of event structures.                  *)
(*         lPoset.eventType L == a type of events with labels of type L,      *)
(*                               i.e. a type equipped with canonical labelled *)
(*                               poset structure instance.                    *)
(*                        lab == labelling function.                          *)
(*                         ca == causality order.                             *)
(*                        sca == strict causality order.                      *)
(*                     x <= y == x preceds y in causality order.              *)
(*                               All conventional order notations are         *)
(*                               defined as well.                             *)
(*                                                                            *)
(*      lPoset.hom E1 E2 == homomorphism between lposets E1 and E2, that is   *)
(*                          label preserving monotone function.               *)
(*      lPoset.bij E1 E2 == bijective homomorphism between lposets E1 and E2. *)
(*      lPoset.emb E1 E2 == embedding between lposets E1 and E2, that is      *)
(*                          order-reflecting homomorphism.                    *)
(*      lPoset.iso E1 E2 == isomorphism between lposets E1 and E2, that is    *)
(*                          bijective order-reflecting homomorphism.          *)
(*                                                                            *)
(* Additionally, this file provides notations for homomorphisms which can     *)
(* be used by importing corresponding module: Import lPoset.Mod.Syntax        *)
(* for Mod in {Hom, Bij, Emb, Iso}.                                           *)
(*                   E1 ~> E2 == homomorphism.                                *)
(*                   E1 ≃> E2 == bijective homomorphism.                      *)
(*                   E1 ≈> E2 == embedding.                                   *)
(*                   E1 ~= E2 == isomorphism.                                 *)
(*                                                                            *)
(* Each module Mod in {Hom, Bij, Emb, Iso} also defines combinators which     *)
(* can be used to build morphisms compositonally.                             *)
(*          lPoset.Mod.id     == identity morphism.                           *)
(*          lPoset.Mod.sy f   == inverse morphisms (for Iso only).            *)
(*          lPoset.Mod.tr f g == composition of morphisms (g \o f).           *)
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

Module lPoset.

Module Export lPoset.
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

Lemma idE {E : eventType L} : 
  Hom.apply (id : E ~> E) = ssrfun.id.
Proof. done. Qed.

Definition tr {E1 E2 E3 : eventType L} : (E1 ~> E2) -> (E2 ~> E3) -> (E1 ~> E3).
  move=> f g; exists (g \o f); do 2 constructor=> /=.
  - by move=> e; rewrite !lab_preserv.
  by move=> e1 e2 /(monotone f) /(monotone g).
Defined.

Lemma trE {E1 E2 E3 : eventType L} (f : E1 ~> E2) (g : E2 ~> E3) : 
   Hom.apply (tr f g) = g \o f.
Proof. done. Qed.

End Cat.

Global Opaque id tr.

End Hom.

Module Export Bij.

Module Bij.
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

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Hom.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion apply : type >-> Funclass.
Coercion homType : type >-> Hom.type.
Canonical homType.
End Exports.

End Bij.

Export Bij.Exports.

Section Def.
Context {L : Type} {E1 E2 : eventType L} (f : Bij.type E1 E2).

Definition inv : E2 -> E1 := Bij.g (Bij.class f).

End Def.

Module Export Syntax. 
Notation bij := Bij.type.
Notation "E1 ≃> E2" := (bij E1 E2) (at level 50) : pomset_scope.
End Syntax. 

Module Export Theory.
Section Theory. 
Context {L : Type} {E1 E2 : eventType L} (f : E1 ≃> E2).

Lemma inv_can : 
  cancel f (inv f).
Proof. by case: f => ? [[? []]] ???. Qed.

Lemma can_inv : 
  cancel (inv f) f.
Proof. by case: f => ? [[? []]] ???. Qed.

Lemma event_bij :
  bijective f.
Proof. by case: f => ? [[? []]] g ? ?; exists g. Qed.

End Theory.
End Theory.

Section Cat.
Context {L : Type}.

Definition id {E : eventType L} : E ≃> E.
  by exists id; do 1 constructor=> //; exists id. 
Defined.

Lemma idE {E : eventType L} : 
  Bij.apply (id : E ≃> E) = ssrfun.id.
Proof. done. Qed.

Definition tr {E1 E2 E3 : eventType L} : (E1 ≃> E2) -> (E2 ≃> E3) -> (E1 ≃> E3).
  move=> f g; exists (Hom.tr f g); constructor. 
  - by case: (Hom.tr f g). 
  case: f=> [? [? []]]; case: g=> [? [? []]].
  by move=> g ?? h ??; exists (h \o g)=> /=; apply /can_comp.
Defined.

Lemma trE {E1 E2 E3 : eventType L} (f : E1 ≃> E2) (g : E2 ≃> E3) : 
   Bij.apply (tr f g) = g \o f.
Proof. done. Qed.

End Cat.

Global Opaque id tr.

End Bij.

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
Notation "E1 ≈> E2" := (emb E1 E2) (at level 50) : pomset_scope.
End Syntax. 

Module Export Theory.
Section Theory. 
Context {L : Type} {E1 E2 : eventType L} (f : E1 ≈> E2).

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

Definition id {E : eventType L} : E ≈> E.
  by exists id; do 1 constructor=> //; exists id. 
Defined.

Lemma idE {E : eventType L} : 
  Emb.apply (id : E ≈> E) = ssrfun.id.
Proof. done. Qed.

Definition tr {E1 E2 E3 : eventType L} : (E1 ≈> E2) -> (E2 ≈> E3) -> (E1 ≈> E3).
  move=> f g; exists (Hom.tr f g); constructor. 
  - by case: (Hom.tr f g). 
  by constructor=> e1 e2 /=; do 2 rewrite -(ord_refl).
Defined.

Lemma trE {E1 E2 E3 : eventType L} (f : E1 ≈> E2) (g : E2 ≈> E3) : 
   Emb.apply (tr f g) = g \o f.
Proof. done. Qed.

End Cat.

Global Opaque id tr.

End Emb.

Module Export Iso.

Module Iso.
Section ClassDef. 

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

End ClassDef.

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

End Iso.

Export Iso.Exports.

Module Export Syntax. 
Notation iso := Iso.type.
Notation "E1 ~= E2" := (iso E1 E2) (at level 50) : pomset_scope.
End Syntax. 

Section Cat.
Context {L : Type}.

Definition id {E : eventType L} : E ~= E.
  by exists Bij.id; constructor=> //; case: Bij.id. 
Defined.

Lemma idE {E : eventType L} : 
  Iso.apply (id : E ~= E) = ssrfun.id.
Proof. done. Qed.

Definition sy {E1 E2 : eventType L} : (E1 ~= E2) -> (E2 ~= E1).
  move=> [] f [[]] [] [] HL HM [] g HK HK' [] HR.
  exists g; repeat constructor.
  - by move=> e; rewrite -{2}[e]HK' !HL.
  - by move=> e1 e2; rewrite -{1}[e1]HK' -{1}[e2]HK'; exact/HR.
  - by exists f.
  move=> e1 e2; rewrite -{2}[e1]HK' -{2}[e2]HK'; exact/HM.
Defined.

Lemma syE {E1 E2 : eventType L} (f : E1 ~= E2) : 
  Iso.apply (sy f) = Bij.inv f.
Proof. by move: f=> [] f [[]] [[]] ?? [] g ?? [] ?; rewrite /inv=> //=. Qed.

Definition tr {E1 E2 E3 : eventType L} : (E1 ~= E2) -> (E2 ~= E3) -> (E1 ~= E3).
  move=> f g; exists (Bij.tr f g); constructor.
  - by case: (Bij.tr f g).
  rewrite Hom.trE.
  have ->: (g \o f = Emb.tr f g) by done.
  by case: (Emb.tr f g)=> ? []. 
Defined.

Lemma trE {E1 E2 E3 : eventType L} (f : E1 ~= E2) (g : E2 ~= E3) : 
   Iso.apply (tr f g) = g \o f.
Proof. done. Qed.

Definition of_homs {E1 E2 : eventType L} (f : E1 ~> E2) (g : E2 ~> E1) : 
  cancel f g -> cancel g f -> (E1 ~= E2).
(* --- *)
  move=> HK HK'; exists f.
  repeat constructor; try by move: HK HK'; case: f=> ? [[]]. 
  - by exists g.
  move=> e1 e2; rewrite -{2}[e1]HK -{2}[e2]HK.
  by move: HK HK'; case: g=> ? [[? H]] ?? /= => /H. 
Defined.

Lemma of_homsE {E1 E2 : eventType L} (f : E1 ~> E2) (g : E2 ~= E1) 
               (K : cancel f g) (K' : cancel g f) : 
   Iso.apply (of_homs K K') = f.
Proof. done. Qed.

Lemma of_homs_invE {E1 E2 : eventType L} (f : E1 ~> E2) (g : E2 ~= E1) 
                   (K : cancel f g) (K' : cancel g f) : 
   Bij.inv (of_homs K K') = g.
Proof. done. Qed.

End Cat.

Global Opaque id sy tr of_homs.

End Iso.

Notation hom := Hom.type.
Notation bij := Bij.type.
Notation emb := Emb.type.
Notation iso := Iso.type.

End lPoset.

Export lPoset.lPoset.Exports.
Export lPoset.Def.

Export lPoset.Hom.Hom.Exports.
Export lPoset.Bij.Bij.Exports.
Export lPoset.Emb.Emb.Exports.
Export lPoset.Iso.Iso.Exports.
Export lPoset.Hom.Theory.
Export lPoset.Bij.Theory.
Export lPoset.Emb.Theory.

Notation lposet := (lPoset.eventStruct).


Module Pomset. 

Implicit Types (L : Type).

Import lPoset.Hom.Syntax.
Import lPoset.Iso.Syntax.

Definition iso_inv {L} (P : lPoset.eventType L -> Prop) := 
  forall {E1 E2} (f : E1 ~= E2), P E1 -> P E2.

Record lang L := Lang { 
  apply : lPoset.eventType L -> Prop;
  _     : forall E1 E2 (f : E1 ~= E2), apply E1 -> apply E2;
            
}.

Module Export Exports.
Coercion apply : lang >-> Funclass.
End Exports.

Module Lattice.
Section Lattice.

Context {L : Type}.
Implicit Types (P Q : lang L).

Definition leq P Q := lattice.leq (P : lPoset.eventType L -> Prop) Q.

Definition weq P Q := lattice.weq (P : lPoset.eventType L -> Prop) Q.

Lemma botP : iso_inv (lattice.bot : lPoset.eventType L -> Prop).
Proof. done. Qed.
Canonical bot := Lang (@botP).

Lemma topP : iso_inv (lattice.top : lPoset.eventType L -> Prop).
Proof. done. Qed.
Canonical top := Lang (@topP).

Lemma cupP P Q : iso_inv ((P : lPoset.eventType L -> Prop) ⊔ Q).
Proof. 
  move: P Q=> [] P + [] Q + p q /=.
  rewrite /iso_inv=> HP HQ f []. 
  - by move: (HP _ _ f)=> /[apply] ?; left. 
  by move: (HQ _ _ f)=> /[apply] ?; right. 
Qed.
Canonical cup P Q := Lang (@cupP P Q).

Lemma capP P Q : iso_inv ((P : lPoset.eventType L -> Prop) ⊓ Q).
Proof. 
  move: P Q=> [] P + [] Q + p q /=.
  rewrite /iso_inv=> HP HQ f []. 
  move: (HP _ _ f)=> /[apply] /[swap].
  by move: (HQ _ _ f)=> /[apply] /[swap].
Qed.
Canonical cap P Q := Lang (@capP P Q).

Lemma negP P : iso_inv (neg (P : lPoset.eventType L -> Prop)).
Proof. 
  move: P=> [] P + p q /=.
  rewrite /iso_inv=> HP f.
  apply/contra_not.
  by move: (HP _ _ (lPoset.Iso.sy f)).
Qed.  
Canonical neg P := Lang (@negP P).

End Lattice.

Module Export Exports.

Canonical Structure pomset_lang_lattice_ops L : lattice.ops := 
  lattice.mk_ops (lang L) leq weq cup cap neg bot top.

Global Instance pomset_lang_lattice_morph L : 
  lattice.morphism BDL (@apply L).
Proof. by constructor. Qed.

Global Instance pomset_lang_lattice_laws L : 
  lattice.laws (BDL+STR+CNV+DIV) (@pomset_lang_lattice_ops L).
Proof.
  have H: (lattice.laws BDL (@pomset_lang_lattice_ops L)). 
  - by apply/(laws_of_injective_morphism (@apply L)).
  by constructor; apply H. 
Qed.

End Exports.

End Lattice.

Export Lattice.Exports.

Module Export Def.
Section Def.

Context {L : Type}.
Implicit Types (P Q : lang L).

Definition stronger P Q : Prop := 
  forall p, P p -> exists q, Q q /\ inhabited (q ~> p).

Definition supported P Q : Prop := 
  forall p, P p -> exists q, Q q /\ inhabited (p ~> q).

End Def.
End Def.

Module Export Syntax.
Notation "P ⊑ Q" := (stronger P Q) (at level 69) : pomset_scope.
Notation "P ↪ Q" := (supported P Q) (at level 69) : pomset_scope.
End Syntax.

Module Export Theory.
Section Theory.

Context {L : Type}.
Implicit Types (P Q R : lang L).

Lemma lang_iso_inv P : iso_inv P.
Proof. by case: P. Qed.

Lemma subsumes_subset P Q :
  P ≦ Q -> P ⊑ Q. 
Proof. 
  move=> Hs p Hp; exists p; split; first exact /Hs. 
  constructor; exact/lPoset.Hom.id. 
Qed.
  
Lemma subsumes_refl P : 
  P ⊑ P.
Proof. 
  move=> p HP; exists p; split=> //. 
  constructor; exact/lPoset.Hom.id.
Qed.

Lemma subsumes_trans P Q R : 
  P ⊑ Q -> Q ⊑ R -> P ⊑ R.
Proof. 
  move=> H1 H2 p HP. 
  move: (H1 p HP)=> [q [HQ [f]]].
  move: (H2 q HQ)=> [r [HR [g]]].
  exists r; split=> //; constructor; exact/(lPoset.Hom.tr g f).
Qed.

Lemma supported_subset P Q :
  P ≦ Q -> P ↪ Q. 
Proof. 
  move=> Hs p Hp; exists p; split; first exact /Hs. 
  constructor; exact/lPoset.Bij.id. 
Qed.

Lemma supported_refl P : 
  P ↪ P. 
Proof. 
  move=> p HP; exists p; split=> //.
  constructor; exact/lPoset.Hom.id.
Qed.

Lemma supported_trans P Q R : 
  (P ↪ Q) -> (Q ↪ R) -> (P ↪ R). 
Proof. 
  move=> H1 H2 p HP. 
  move: (H1 p HP)=> [q [HQ [f]]].
  move: (H2 q HQ)=> [r [HR [g]]].
  exists r; split=> //; constructor; exact/(lPoset.Hom.tr f g).
Qed.

End Theory.
End Theory.

End Pomset.

Export Pomset.Exports.
Export Pomset.Lattice.Exports.
Export Pomset.Def.
Export Pomset.Syntax.
Export Pomset.Theory.


Module LLoset.

Module Export LLoset.
Section ClassDef. 

Set Primitive Projections.
Record class_of (E : Type) (L : Type) := Class { 
  base  : Order.Total.class_of E;
  mixin : LPoset.LPoset.mixin_of L base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Order.Total.class_of.

Structure type (L : Type) := Pack { sort; _ : class_of sort L }.

Local Coercion sort : type >-> Sortclass.

Variables (E : Type) (L : Type) (cT : type L).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') L in c.
Definition clone c of phant_id class c := @Pack E c.

Definition pack :=
  fun bE b & phant_id (@LPoset.LPoset.class L bE) b =>
  fun m => Pack (@Class E L b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @Order.POrder.Pack tt cT class.
Definition latticeType := @Lattice.Pack tt cT class.
Definition distrLatticeType := @DistrLattice.Pack tt cT class.
Definition orderType := @Order.Total.Pack tt cT class.
Definition lposetType := 
  @LPoset.LPoset.Pack L cT (LPoset.LPoset.Class (mixin class)).
End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Order.Total.class_of.
Coercion mixin : class_of >-> LPoset.LPoset.mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> Order.POrder.type.
Coercion latticeType : type >-> Lattice.type.
Coercion distrLatticeType : type >-> DistrLattice.type.
Coercion orderType : type >-> Order.Total.type.
Coercion lposetType : type >-> LPoset.LPoset.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical latticeType.
Canonical distrLatticeType.
Canonical orderType.
Canonical lposetType.
Notation LLosetType E L m := (@pack E L _ _ id m).
End Exports.

End LLoset.

Notation eventType := LLoset.type.
Notation eventStruct := LLoset.class_of.

End LLoset.

Export LLoset.LLoset.Exports.


Module Export Lin.

Section Def. 
Context {L : Type} (E : LPoset.eventType L).

Record lin (E' : LLoset.eventType L) : Prop := 
  is_lin { _ : LPoset.hom E E' }.

End Def.

Import LPoset.Hom.Syntax.

Section Theory. 
Context {L : Type} {E1 E2 : LPoset.eventType L}.

Lemma hom_lin : (E1 ~> E2) -> lin E2 ≦ lin E1.
Proof. move=> f E2' [] g; constructor; exact /(LPoset.Hom.tr f g). Qed.

End Theory.  

End Lin.
