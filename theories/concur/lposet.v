From RelationAlgebra Require Import lattice monoid rel boolean.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun.
From mathcomp Require Import eqtype choice order seq tuple path div.
From mathcomp Require Import fintype finfun fingraph finmap.
From eventstruct Require Import utils inhtype order.

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
(*     lPoset.pref E1 E2 == prefix homomorphism between lposets E1 and E2     *)
(*                          that is homomorphism that maps E1 into the E2's   *)
(*                          prefix                                            *)
(*      lPoset.iso E1 E2 == isomorphism between lposets E1 and E2, that is    *)
(*                          bijective order-reflecting homomorphism.          *)
(* By importing module lPoset.Syntax one can use the following notations.     *)
(*                   {hom  E1 -> E2} == homomorphism.                         *)
(*                   {ihom E1 -> E2} == injective homomorphism.               *)
(*                   {bhom E1 -> E2} == bijective homomorphism.               *)
(*                   {emb  E1 -> E2} == embedding.                            *)
(*                   {pref E1 -> E2} == prefix homomorphism.                  *)
(*                   {iso  E1 -> E2} == isomorphism.                          *)
(* A notation [hom of f] can be used to build a homomorphism out of function, *)
(* provided that there is a canonical instance of homomorphism for f.         *)
(* In particular:                                                             *)
(*                   [hom of idfun]  == denotes identity homomorphism.        *)
(*                   [hom of f \o g] == denotes composition of homomorphisms. *)
(* Similar notations are available for ihom, bhom, emb, pref, iso.            *)
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

End Def.
End Def.

Prenex Implicits lab ca sca.

Module Export Hom.

Module Hom.
Section ClassDef. 
(* TODO: homomorphism between pomsets labelled by different labels? *)
Context {L : Type} (E1 E2 : eventType L).
Implicit Types (f : E1 -> E2).

Definition axiom f := 
  [/\ { mono f : e / lab e }
    & { homo f : e1 e2 / e1 <= e2 }
  ].

Structure type := Pack { apply ; _ : axiom apply }.

Local Coercion apply : type >-> Funclass.

Definition mk h mkH : type :=
  mkH (let: Pack _ c := h return @axiom h in c).

Definition type_of (_ : phant (E1 -> E2)) := type.

End ClassDef.

Module Export Exports.
Coercion apply : type >-> Funclass.
End Exports.

End Hom.

Export Hom.Exports.

Module Export Syntax. 
Notation hom := Hom.type.
Notation "{ 'hom' T }" := (@Hom.type_of _ _ _ (Phant T)) : lposet_scope.
Notation "[ 'hom' 'of' f ]" := 
  (Hom.mk (fun hCls => @Hom.Pack _ _ _ f hCls))
  (at level 0, format "[ 'hom'  'of'  f ]") : lposet_scope.
End Syntax.

Module Export Theory.
Section Theory. 
Context {L : Type} {E1 E2 : eventType L}. 
Implicit Types (f : {hom E1 -> E2}).

Lemma lab_preserving f :
  { mono f : e / lab e }.
Proof. by case: f=> ? []. Qed.

Lemma ca_monotone f :
  { homo f : e1 e2 / e1 <= e2 }.
Proof. by case: f=> ? []. Qed.

End Theory.
End Theory.

Module Build.
Section Build.
Context {L : Type} {E E1 E2 E3 : eventType L}.
Implicit Types (f : {hom E2 -> E3}) (g : {hom E1 -> E2}).

Lemma id_axiom : Hom.axiom (@idfun E).
Proof. by split; done. Qed.

Lemma comp_axiom f g : Hom.axiom (comp f g).
Proof. 
  repeat constructor=> /=.
  - by move=> e; rewrite !lab_preserving.
  by move=> e1 e2 /(ca_monotone g) /(ca_monotone f).
Qed.

End Build.

Module Export Exports.
Section Exports.
Context {L : Type} {E E1 E2 E3 : eventType L}.
Implicit Types (f : {hom E2 -> E3}) (g : {hom E1 -> E2}).

Canonical id_hom := Hom.Pack (@id_axiom L E).
Canonical comp_hom f g := Hom.Pack (comp_axiom f g).

End Exports.
End Exports. 

End Build.

End Hom.

Module Export iHom.

Module iHom.
Section ClassDef. 
Context {L : Type} (E1 E2 : eventType L).
Implicit Types (f : E1 -> E2).

Definition axiom f := 
  [/\ { mono f : e / lab e }
    , { homo f : e1 e2 / e1 <= e2 }
    & injective f
  ].

Structure type := Pack { apply ; _ : axiom apply }.

Local Coercion apply : type >-> Funclass.

Definition mk h mkH : type :=
  mkH (let: Pack _ c := h return @axiom h in c).

Definition type_of (_ : phant (E1 -> E2)) := type.

Lemma hom_axiom_of f : axiom f -> Hom.axiom f.
Proof. by move=> []. Qed.

Lemma ihom_axiom_of f : Hom.axiom f -> injective f -> axiom f.
Proof. by move=> []. Qed.

Variables (cT : type).

Lemma homAxiom : Hom.axiom cT.
Proof. by case: cT=> /= ? /hom_axiom_of. Qed.

Definition homType := Hom.Pack homAxiom.

End ClassDef.

Module Export Exports.
Coercion apply : type >-> Funclass.
Coercion homType : type >-> Hom.type.
Canonical homType.
End Exports.

End iHom.

Export iHom.Exports.

Module Export Syntax. 
Notation ihom := iHom.type.
Notation "{ 'ihom' T }" := (@iHom.type_of _ _ _ (Phant T)) : lposet_scope.
Notation "[ 'ihom' 'of' f ]" := 
  (iHom.mk (fun hCls => @iHom.Pack _ _ _ f hCls))
  (at level 0, format "[ 'ihom'  'of'  f ]") : lposet_scope.
End Syntax. 

Module Export Theory.
Section Theory. 
Context {L : Type} {E1 E2 : eventType L}.
Implicit Types (f : {ihom  E1 -> E2}).

Lemma ihom_inj f : 
  injective f.
Proof. by case: f => ? []. Qed.

Lemma sca_monotone f :
  { homo f : e1 e2 / e1 < e2 }.
Proof. 
  move=> ?; apply/inj_homo_lt=> //. 
  - exact/ihom_inj. 
  exact/ca_monotone.
Qed.

End Theory.
End Theory.

Module Build.
Section Build.
Context {L : Type} {E E1 E2 E3 : eventType L}.
Implicit Types (f : {ihom E2 -> E3}) (g : {ihom E1 -> E2}).

Lemma id_axiom : iHom.axiom (@idfun E).
Proof. by repeat constructor=> //. Qed.

Lemma comp_axiom f g : iHom.axiom (f \o g).
Proof. 
  apply/iHom.ihom_axiom_of.
  - exact/(Hom.Build.comp_axiom f g).
  by move=> x y /= /ihom_inj /ihom_inj.
Qed.

End Build.
Module Export Exports.
Section Exports.
Context {L : Type} {E E1 E2 E3 : eventType L}.
Implicit Types (f : {ihom E2 -> E3}) (g : {ihom E1 -> E2}).

Canonical id_hom := iHom.Pack (@id_axiom L E).
Canonical comp_hom f g := iHom.Pack (comp_axiom f g).

End Exports.
End Exports. 

End Build.

End iHom.


Module Export bHom.

Module bHom.
Section ClassDef. 
Context {L : Type} (E1 E2 : eventType L).
Implicit Types (f : E1 -> E2).

Definition axiom f := 
  [/\ { mono f : e / lab e }
    , { homo f : e1 e2 / e1 <= e2 }
    & bijective f
  ].

Structure type := Pack { apply ; _ : axiom apply }.

Local Coercion apply : type >-> Funclass.

Definition mk h mkH : type :=
  mkH (let: Pack _ c := h return @axiom h in c).

Definition type_of (_ : phant (E1 -> E2)) := type.

Lemma hom_axiom_of f : axiom f -> Hom.axiom f.
Proof. by move=> []. Qed.

Lemma ihom_axiom_of f : axiom f -> iHom.axiom f.
Proof. by move=> [] ?? /bij_inj. Qed.

Lemma bhom_axiom_of f : Hom.axiom f -> bijective f -> axiom f.
Proof. by move=> []. Qed.

Variables (cT : type).

Lemma homAxiom : Hom.axiom cT.
Proof. by case: cT=> /= ? /hom_axiom_of. Qed.

Lemma ihomAxiom : iHom.axiom cT.
Proof. by case: cT=> /= ? /ihom_axiom_of. Qed.

Definition homType  :=  Hom.Pack  homAxiom.
Definition ihomType := iHom.Pack ihomAxiom.

End ClassDef.

Module Export Exports.
Coercion apply : type >-> Funclass.
Coercion  homType : type >-> Hom.type.
Coercion ihomType : type >-> iHom.type.
Canonical  homType.
Canonical ihomType.
End Exports.

End bHom.

Export bHom.Exports.

Module Export Syntax. 
Notation bhom := bHom.type.
Notation "{ 'bhom' T }" := (@bHom.type_of _ _ _ (Phant T)) : lposet_scope.
Notation "[ 'bhom' 'of' f ]" := 
  (bHom.mk (fun hCls => @bHom.Pack _ _ _ f hCls))
  (at level 0, format "[ 'bhom'  'of'  f ]") : lposet_scope.
End Syntax. 

Module Export Theory.
Section Theory. 
Context {L : Type} {E1 E2 : eventType L}.
Implicit Types (f : {bhom  E1 -> E2}).

Lemma bhom_bij f :
  bijective f.
Proof. by case: f => ? []. Qed.

End Theory.
End Theory.

Module Build.
Section Build.
Context {L : Type} {E E1 E2 E3 : eventType L}.
Implicit Types (f : {bhom E2 -> E3}) (g : {bhom E1 -> E2}).

Lemma id_axiom : bHom.axiom (@idfun E).
Proof. by constructor=> //; exists id. Qed.

Lemma comp_axiom f g : bHom.axiom (f \o g).
Proof. 
  apply/bHom.bhom_axiom_of.
  - exact/Hom.Build.comp_axiom.
  apply/bij_comp; exact/bhom_bij.  
Qed.

End Build.

Module Export Exports.
Section Exports.
Context {L : Type} {E E1 E2 E3 : eventType L}.
Implicit Types (f : {bhom E2 -> E3}) (g : {bhom E1 -> E2}).

Canonical id_bhom := bHom.Pack (@id_axiom L E).
Canonical comp_bhom f g := bHom.Pack (comp_axiom f g).

End Exports.
End Exports. 
End Build.

End bHom.


Module Export Emb.

Module Emb.
Section ClassDef. 
Context {L : Type} (E1 E2 : eventType L).
Implicit Types (f : E1 -> E2).

Definition axiom f := 
  [/\ { mono f : e / lab e }
    & { mono f : e1 e2 / e1 <= e2 }
  ].

Structure type := Pack { apply ; _ : axiom apply }.

Local Coercion apply : type >-> Funclass.

Definition mk h mkH : type :=
  mkH (let: Pack _ c := h return @axiom h in c).

Definition type_of (_ : phant (E1 -> E2)) := type.

Lemma hom_axiom_of f : axiom f -> Hom.axiom f.
Proof. by move=> [] ? /mono2W. Qed.

Lemma ihom_axiom_of f : axiom f -> iHom.axiom f.
Proof. by move=> [] ? /[dup] /mono2W ? /inc_inj. Qed.

Lemma emb_axiom_of f : Hom.axiom f -> {ahomo f : e1 e2 / e1 <= e2} -> axiom f.
Proof. move=> [] ???; split=> //; exact/le_homo_mono. Qed.

Variables (cT : type).

Lemma homAxiom : Hom.axiom cT.
Proof. by case: cT=> /= ? /hom_axiom_of. Qed.

Lemma ihomAxiom : iHom.axiom cT.
Proof. by case: cT=> /= ? /ihom_axiom_of. Qed.

Definition homType  :=  Hom.Pack  homAxiom.
Definition ihomType := iHom.Pack ihomAxiom.

End ClassDef.

Module Export Exports.
Coercion apply : type >-> Funclass.
Coercion  homType : type >-> Hom.type.
Coercion ihomType : type >-> iHom.type.
Canonical  homType.
Canonical ihomType.
End Exports.

End Emb.

Export Emb.Exports.

Module Export Syntax. 
Notation emb := Emb.type.
Notation "{ 'emb' T }" := (@Emb.type_of _ _ _ (Phant T)) : lposet_scope.
Notation "[ 'emb' 'of' f ]" := 
  (Emb.mk (fun hCls => @Emb.Pack _ _ _ f hCls))
  (at level 0, format "[ 'emb'  'of'  f ]") : lposet_scope.
End Syntax. 

Module Export Theory.
Section Theory. 
Context {L : Type} {E1 E2 : eventType L}.
Implicit Types (f : {emb  E1 -> E2}).

Lemma ca_reflecting f :
  { mono f : e1 e2 / e1 <= e2 }.
Proof. by case: f=> ? []. Qed.

End Theory.
End Theory.

Module Build.
Section Build.
Context {L : Type} {E E1 E2 E3 : eventType L}.
Implicit Types (f : {emb E2 -> E3}) (g : {emb E1 -> E2}).

Lemma id_axiom : Emb.axiom (@idfun E).
Proof. by repeat constructor. Qed.

Lemma comp_axiom f g : Emb.axiom (f \o g).
Proof. 
  apply/Emb.emb_axiom_of.
  - exact/Hom.Build.comp_axiom.
  by move=> x y /=; rewrite (ca_reflecting f) (ca_reflecting g).
Qed.

End Build.

Module Export Exports.
Section Exports.
Context {L : Type} {E E1 E2 E3 : eventType L}.
Implicit Types (f : {emb E2 -> E3}) (g : {emb E1 -> E2}).

Canonical id_emb := Emb.Pack (@id_axiom L E).
Canonical comp_emb f g := Emb.Pack (comp_axiom f g).

End Exports.
End Exports.
End Build.

End Emb.

Module Export Pref.

Module Pref.
Section ClassDef. 
Context {L : Type} (E1 E2 : eventType L).
Implicit Types (f : E1 -> E2).

Definition axiom f := 
  [/\ { mono f : e / lab e }
    , { mono f : e1 e2 / e1 <= e2 }
    & dw_surjective f
  ].

Structure type := Pack { apply ; _ : axiom apply }.

Local Coercion apply : type >-> Funclass.

Definition mk h mkH : type :=
  mkH (let: Pack _ c := h return @axiom h in c).

Definition type_of (_ : phant (E1 -> E2)) := type.

Lemma hom_axiom_of f : axiom f -> Hom.axiom f.
Proof. by move=> [] ? /mono2W. Qed.

Lemma ihom_axiom_of f : axiom f -> iHom.axiom f.
Proof. by move=> [] ? /[dup] /mono2W ? /inc_inj. Qed.

Lemma emb_axiom_of f : axiom f -> Emb.axiom f.
Proof. by move=> [] ?. Qed.

Lemma pref_axiom_of f : Emb.axiom f -> dw_surjective f -> axiom f.
Proof. by move=> []. Qed.

Variables (cT : type).

Lemma homAxiom : Hom.axiom cT.
Proof. by case: cT=> /= ? /hom_axiom_of. Qed.

Lemma ihomAxiom : iHom.axiom cT.
Proof. by case: cT=> /= ? /ihom_axiom_of. Qed.

Lemma embAxiom : Emb.axiom cT.
Proof. by case: cT=> /= ? /emb_axiom_of. Qed.

Definition  homType :=  Hom.Pack  homAxiom.
Definition ihomType := iHom.Pack ihomAxiom.
Definition  embType :=  Emb.Pack  embAxiom.

End ClassDef.

Module Export Exports.
Coercion apply : type >-> Funclass.
Coercion  homType : type >-> Hom.type.
Coercion ihomType : type >-> iHom.type.
Coercion  embType : type >-> Emb.type.
Canonical  homType.
Canonical ihomType.
Canonical  embType.
End Exports.

End Pref.

Export Pref.Exports.

Module Export Syntax. 
Notation pref := Pref.type.
Notation "{ 'pref' T }" := (@Pref.type_of _ _ _ (Phant T)) : lposet_scope.
Notation "[ 'pref' 'of' f ]" := 
  (Pref.mk (fun hCls => @Pref.Pack _ _ _ f hCls))
  (at level 0, format "[ 'pref'  'of'  f ]") : lposet_scope.
End Syntax. 

Module Export Theory.
Section Theory. 
Context {L : Type} {E1 E2 : eventType L}.
Implicit Types (f : {pref E1 -> E2}).

Lemma ca_surjective f :
  dw_surjective f.
Proof. by case f=> ? []. Qed.

End Theory.
End Theory.

Module Build.
Section Build.
Context {L : Type} {E E1 E2 E3 : eventType L}.
Implicit Types (f : {pref E2 -> E3}) (g : {pref E1 -> E2}).

Lemma id_axiom : Pref.axiom (@idfun E).
Proof. by split=> // e e' /= _; exists e'. Qed.

Lemma comp_axiom f g : Pref.axiom (f \o g).
Proof. 
  apply/Pref.pref_axiom_of.
  - exact/Emb.Build.comp_axiom.
  move=> e e' /= /[dup] /ca_surjective[x] <-.
  rewrite inE (ca_reflecting f)=> /ca_surjective[y] <-.
  by exists y.
Qed.

End Build.
Module Export Exports.
Section Exports.
Context {L : Type} {E E1 E2 E3 : eventType L}.
Implicit Types (f : {pref E2 -> E3}) (g : {pref E1 -> E2}).

Canonical id_pref := Pref.Pack (@id_axiom L E).
Canonical comp_pref f g := Pref.Pack (comp_axiom f g).

End Exports.
End Exports.
End Build.

End Pref.

Module Export Iso.

Module Iso.
Section ClassDef. 
Context {L : Type} (E1 E2 : eventType L).
Implicit Types (f : E1 -> E2).

Definition axiom f := 
  [/\ { mono f : e / lab e }
    , { mono f : e1 e2 / e1 <= e2 }
    & bijective f
  ].

Structure type := Pack { apply ; _ : axiom apply }.

Local Coercion apply : type >-> Funclass.

Definition mk h mkH : type :=
  mkH (let: Pack _ c := h return @axiom h in c).

Definition type_of (_ : phant (E1 -> E2)) := type.

Lemma hom_axiom_of f : axiom f -> Hom.axiom f.
Proof. by move=> [] ? /mono2W. Qed.

Lemma ihom_axiom_of f : axiom f -> iHom.axiom f.
Proof. by move=> [] ? /[dup] /mono2W ? /inc_inj. Qed.

Lemma bhom_axiom_of f : axiom f -> bHom.axiom f.
Proof. by move=> [] ? /mono2W. Qed.

Lemma emb_axiom_of f : axiom f -> Emb.axiom f.
Proof. by move=> [] ?. Qed.

Lemma pref_axiom_of f : axiom f -> Pref.axiom f.
Proof. by move=> [] ?? /bij_surj /surj_dw_surj. Qed.

Lemma iso_axiom_of f : bHom.axiom f -> {ahomo f : e1 e2 / e1 <= e2} -> axiom f.
Proof. move=> [] ???; split=> //; exact/le_homo_mono. Qed.

Variables (cT : type).

Lemma homAxiom : Hom.axiom cT.
Proof. by case: cT=> /= ? /hom_axiom_of. Qed.

Lemma ihomAxiom : iHom.axiom cT.
Proof. by case: cT=> /= ? /ihom_axiom_of. Qed.

Lemma bhomAxiom : bHom.axiom cT.
Proof. by case: cT=> /= ? /bhom_axiom_of. Qed.

Lemma embAxiom : Emb.axiom cT.
Proof. by case: cT=> /= ? /emb_axiom_of. Qed.

Lemma prefAxiom : Pref.axiom cT.
Proof. by case: cT=> /= ? /pref_axiom_of. Qed.

Definition  homType :=  Hom.Pack  homAxiom.
Definition ihomType := iHom.Pack ihomAxiom.
Definition bhomType := bHom.Pack bhomAxiom.
Definition  embType :=  Emb.Pack  embAxiom.
Definition prefType := Pref.Pack prefAxiom.

End ClassDef.

Module Export Exports.
Coercion apply : type >-> Funclass.
Coercion homType  : type >-> Hom.type.
Coercion ihomType : type >-> iHom.type.
Coercion bhomType : type >-> bHom.type.
Coercion embType  : type >-> Emb.type.
Coercion prefType  : type >-> Pref.type.
Canonical homType.
Canonical ihomType.
Canonical bhomType.
Canonical embType.
Canonical prefType.
End Exports.

End Iso.

Export Iso.Exports.

Module Export Syntax. 
Notation iso := Iso.type.
Notation "{ 'iso' T }" := (@Iso.type_of _ _ _ (Phant T)) : lposet_scope.
Notation "[ 'iso' 'of' f ]" := 
  (Iso.mk (fun hCls => @Iso.Pack _ _ _ f hCls))
  (at level 0, format "[ 'iso'  'of'  f ]") : lposet_scope.
End Syntax. 

Module Build.
Section Build.
Context {L : Type} {E E1 E2 E3 : eventType L}.
Implicit Types (f : {iso E2 -> E3}) (g : {iso E1 -> E2}).

Lemma id_axiom : Iso.axiom (@idfun E).
Proof. by repeat constructor=> //; exists id. Qed.

Lemma comp_axiom f g : Iso.axiom (f \o g).
Proof. 
  apply/Iso.iso_axiom_of.
  - exact/(bHom.Build.comp_axiom f g).
  by move=> x y /=; rewrite (ca_reflecting f) (ca_reflecting g).
Qed.

End Build.

Module Export Exports.
Section Exports.
Context {L : Type} {E E1 E2 E3 : eventType L}.
Implicit Types (f : {iso E2 -> E3}) (g : {iso E1 -> E2}).

Canonical id_iso := Iso.Pack (@id_axiom L E).
Canonical comp_iso f g := Iso.Pack (comp_axiom f g).

End Exports.
End Exports.

End Build.

End Iso.

Notation hom := Hom.type.
Notation ihom := iHom.type.
Notation bhom := bHom.type.
Notation emb := Emb.type.
Notation pref := Pref.type.
Notation iso := Iso.type.

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
Export lPoset.Pref.Pref.Exports.
Export lPoset.Iso.Iso.Exports.

Export lPoset.Hom.Build.Exports.
Export lPoset.iHom.Build.Exports.
Export lPoset.bHom.Build.Exports.
Export lPoset.Emb.Build.Exports.
Export lPoset.Pref.Build.Exports.
Export lPoset.Iso.Build.Exports.

Export lPoset.Hom.Theory.
Export lPoset.iHom.Theory.
Export lPoset.bHom.Theory.
Export lPoset.Emb.Theory.
Export lPoset.Pref.Theory.
(* Export lPoset.Iso.Theory. *)

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
Import lPoset.Pref.Syntax.

End lLoset.

Export lLoset.lLoset.Exports.


Module lDwFinPoset.

Module lDwFinPoset.
Section ClassDef. 

Set Primitive Projections.
Record class_of (E : Type) (L : Type) := Class { 
  base  : DwFinPOrder.DwFinPOrder.class_of E;
  mixin : lPoset.lPoset.mixin_of L base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> DwFinPOrder.DwFinPOrder.class_of.

Local Coercion base2 E L (c : class_of E L) : 
  lPoset.lPoset.class_of E L := 
    lPoset.lPoset.Class (mixin c).

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
Definition porderType := @Order.POrder.Pack tt cT class.
Definition dwFinPOrderType := @DwFinPOrder.DwFinPOrder.Pack cT class.
Definition lposetType := @lPoset.lPoset.Pack L cT class.
End ClassDef.

Module Export Exports.
Coercion base : class_of >-> DwFinPOrder.DwFinPOrder.class_of.
Coercion base2 : class_of >-> lPoset.lPoset.class_of.
Coercion mixin : class_of >-> lPoset.lPoset.mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> Order.POrder.type.
Coercion dwFinPOrderType : type >-> DwFinPOrder.DwFinPOrder.type.
Coercion lposetType : type >-> lPoset.lPoset.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical dwFinPOrderType.
Canonical lposetType.
Notation lDwFinPosetType E L m := (@pack E L _ _ id m).
End Exports.

End lDwFinPoset.

Export lDwFinPoset.Exports.

Notation eventType := lDwFinPoset.type.
Notation eventStruct := lDwFinPoset.class_of.

End lDwFinPoset.

Export lDwFinPoset.lDwFinPoset.Exports.


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

Section Hom.
Context {L : eqType}. 
Implicit Types (E : eventType L).

Definition hom_pred {E1 E2} (f : {ffun E1 -> E2}) := 
  [&& [forall e, lab (f e) == lab e]  
    & [forall e1, forall e2, (e1 <= e2) ==> (f e1 <= f e2)]
  ].

Definition hom_rel E1 E2 := ??|{ffun E1 -> E2 | hom_pred}|.

Section Def.
Context {E1 E2 : eventType L}.
Implicit Types (f : {ffun E1 -> E2 | hom_pred}).
Implicit Types (g : {hom E1 -> E2}).

(* TODO: try to shorten copy-paste in hom definitions, 
 *   try to generalize to arbitary pair of P and p, 
 *   s.t. reflect P p  
 *)

(* TODO: try alternative notations: 
 *   {hom E1 -> E2} for homomorphism
 *   {fhom E1 -> E2} for finite homomorphism
 *)

Lemma fhom_lab_preserving f :
  [forall e, lab (f e) == lab e].
Proof. by case: f=> [{}f] /= /andP[]. Qed.

Lemma fhom_ca_monotone f :
  [forall e1, forall e2, (e1 <= e2) ==> (f e1 <= f e2)].
Proof. by case: f=> [{}f] /= /andP[]. Qed.

Lemma hom_pred_of_hom g : 
  hom_pred [ffun x => g x].
Proof. 
  apply/andP; split.
  - apply/forallP=> e; rewrite ffunE /=. 
    by apply/eqP/(lab_preserving g).
  apply/forallP=> e1; apply/forallP=> e2.
  apply/implyP; rewrite !ffunE /=.
  by apply/(ca_monotone g).
Qed.

Definition fhom_of_hom g : {ffun E1 -> E2 | hom_pred} := 
  Sub [ffun x => g x] (hom_pred_of_hom g).

Lemma hom_mixin f : 
  lPoset.Hom.Hom.mixin_of f.
Proof.
  constructor.
  - apply/fin_lab_preservingP/fhom_lab_preserving.
  apply/fin_ca_monotoneP/fhom_ca_monotone.
Qed.

Definition hom_of_fhom f : {hom E1 -> E2} :=
  lPoset.Hom.Hom.Pack (lPoset.Hom.Hom.Class (hom_mixin f)).

Definition ohom f : option {hom  E1 -> E2} := 
  omap hom_of_fhom (insub [ffun x => f x]).

End Def. 

Section Theory.

Lemma fhomP E1 E2 :
  reflect ?|{hom E1 -> E2}| ??|{ffun E1 -> E2 | hom_pred}|.
Proof.
  apply/equivP; first exact/fin_inhP.
  exact/(inh_iff hom_of_fhom fhom_of_hom). 
Qed.

Lemma hom_refl : reflexive hom_rel.
Proof. apply/(is_inh_refl fhomP)=> E; exact/[hom of idfun : E -> E]. Qed.

Lemma hom_trans : transitive hom_rel.
Proof. apply/(is_inh_trans fhomP)=> ??? f g; exact/[hom of g \o f]. Qed.

End Theory.

End Hom.

Prenex Implicits hom_pred hom_of_fhom fhom_of_hom ohom.

Section iHom.
Context {L : eqType}.
Implicit Types (E : eventType L).

Definition ihom_pred {E1 E2} (f : {ffun E1 -> E2}) := 
  hom_pred f && injectiveb f.

Definition ihom_rel E1 E2 := ??|{ffun E1 -> E2 | ihom_pred}|.

Section Def.
Context {E1 E2 : eventType L}.
Implicit Types (f : {ffun E1 -> E2 | ihom_pred}).
Implicit Types (g : {ihom E1 -> E2}).

Lemma fihom_inj f :
  injective f.
Proof. by case: f=> [{}f] /= /andP[] ? /injectiveP. Qed.

Lemma ihom_pred_of_ihom g : 
  ihom_pred [ffun x => g x].
Proof. 
  apply/andP; split; first exact/hom_pred_of_hom.
  apply/injectiveP=> x y; rewrite !ffunE; exact/ihom_inj.
Qed.

Definition fhom_of_fihom f : {ffun E1 -> E2 | hom_pred} := 
  Sub _ (proj1 (andP (valP f))).

Definition fihom_of_ihom g : {ffun E1 -> E2 | ihom_pred} := 
  Sub [ffun x => g x] (ihom_pred_of_ihom g).

Lemma ihom_mixin f : 
  lPoset.iHom.iHom.mixin_of f.
Proof. constructor; exact/fihom_inj. Qed.

Definition ihom_of_fihom f : {ihom E1 -> E2} :=
  let base  := lPoset.Hom.Hom.class (hom_of_fhom (fhom_of_fihom f)) in
  let mixin := ihom_mixin f in 
  lPoset.iHom.iHom.Pack (lPoset.iHom.iHom.Class base mixin).

Definition oihom f : option {ihom E1 -> E2} := 
  omap ihom_of_fihom (insub [ffun x => f x]).

End Def.

Section Theory.

Lemma fihomP E1 E2 :
  reflect ?|{ihom E1 -> E2}| ??|{ffun E1 -> E2 | ihom_pred}|.
Proof.
  apply/equivP; first exact/fin_inhP.
  apply/(inh_iff ihom_of_fihom).  
  exact/fihom_of_ihom.
Qed.

Lemma ihom_refl : reflexive ihom_rel.
Proof. apply/(is_inh_refl fihomP)=> E; exact/[ihom of idfun : E -> E]. Qed.

Lemma ihom_trans : transitive ihom_rel.
Proof. apply/(is_inh_trans fihomP)=> ??? f g; exact/[ihom of g \o f]. Qed.

Lemma fihom_ca_reflecting {E1 E2} (f : {ihom E1 -> E2}) (g : {ihom E2 -> E1}) :
  { mono f : e1 e2 / e1 <= e2 }.
Proof. 
  move=> e1 e2; apply/idP/idP; last first.
  - exact/(ca_monotone f).
  pose h := [ihom of g \o f]. 
  have: injective h by exact/ihom_inj.
  move=> /cycle_orbit cyc.
  pose o1 := order h e1.
  pose o2 := order h e2.
  pose o  := lcmn o1 o2.
  have {2}<-: iter ((o %/ o1) * o1) h e1 = e1.
  - rewrite iter_mul_eq /o1 //.
    apply/(iter_order_cycle (cyc e1)); exact/in_orbit.
  have {2}<-: iter ((o %/ o2) * o2) h e2 = e2.
  - rewrite iter_mul_eq /o2 //.
    apply/(iter_order_cycle (cyc e2)); exact/in_orbit.
  rewrite !divnK; last first. 
  - exact/dvdn_lcml.
  - exact/dvdn_lcmr.
  have: o = lcmn o1 o2 by done.
  case o=> [|{}o].
  - move=> /esym /eqP. 
    rewrite eqn0Ngt lcmn_gt0 negb_and ?/o1 ?/o2.
    move: (order_gt0 h e1) (order_gt0 h e2).
    by move=> ++ /orP[/negP|/negP]. 
  rewrite !iterSr=> ??; apply/homo_iter.
  - exact/(ca_monotone h).
  exact/(ca_monotone g).
Qed.

End Theory.

End iHom.

Prenex Implicits ihom_pred ihom_of_fihom fihom_of_ihom oihom.

Section bHom.
Context {L : eqType}.
Implicit Types (E : eventType L).

Definition bhom_pred {E1 E2} (f : {ffun E1 -> E2}) := 
  ihom_pred f && (#|E2| <= #|E1|).

Definition bhom_rel E1 E2 := ??|{ffun E1 -> E2 | bhom_pred}|.

Section Def.
Context {E1 E2 : eventType L}.
Implicit Types (f : {ffun E1 -> E2 | bhom_pred}).
Implicit Types (g : {bhom E1 -> E2}).

Lemma fbhom_bij f :
  bijective f.
Proof. 
  case: f=> [{}f] /= /andP[] /andP[] ?.
  move=> /injectiveP; exact/inj_card_bij.  
Qed.

Lemma bhom_pred_of_bhom g : 
  bhom_pred [ffun x => g x].
Proof. 
  apply/andP; split; first exact/ihom_pred_of_ihom.
  by apply/eq_leq/esym/bij_eq_card/(bhom_bij g).
Qed.

Definition fihom_of_fbhom f : 
  {ffun E1 -> E2 | ihom_pred} := Sub _ (proj1 (andP (valP f))).

Definition fbhom_of_bhom g : {ffun E1 -> E2 | bhom_pred} := 
  Sub [ffun x => g x] (bhom_pred_of_bhom g).


Lemma bhom_mixin f : 
  lPoset.bHom.bHom.mixin_of f.
Proof. 
  move: (valP f)=> /andP[] /andP[] ? /injectiveP Hi Hn.
  pose g := (fun y => iinv (inj_card_onto Hi Hn y)).
  by exists g=> y; rewrite /g ?iinv_f ?f_iinv.
Qed.

Definition bhom_of_fbhom f : {bhom E1 -> E2} :=
  let fihom := fihom_of_fbhom f in
  let base  := lPoset.Hom.Hom.class (hom_of_fhom (fhom_of_fihom fihom)) in
  let mixin := bhom_mixin f in 
  lPoset.bHom.bHom.Pack (lPoset.bHom.bHom.Class base mixin).

Definition obhom f : option ({bhom  E1 -> E2}) := 
  omap bhom_of_fbhom (insub [ffun x => f x]).

End Def.

Section Theory.

Lemma fbhomP E1 E2 :
  reflect ?|{bhom E1 -> E2}| ??|{ffun E1 -> E2 | bhom_pred}|.
Proof.
  apply/equivP; first exact/fin_inhP.
  apply/(inh_iff bhom_of_fbhom).  
  exact/fbhom_of_bhom.
Qed.

Lemma bhom_refl : reflexive bhom_rel.
Proof. apply/(is_inh_refl fbhomP)=> E; exact/[bhom of idfun : E -> E]. Qed.

Lemma bhom_trans : transitive bhom_rel.
Proof. apply/(is_inh_trans fbhomP)=> ??? f g; exact/[bhom of g \o f]. Qed.

End Theory. 

End bHom.

Prenex Implicits bhom_pred bhom_of_fbhom fbhom_of_bhom obhom.

Section Emb.
Context {L : eqType}.
Implicit Types (E : eventType L).

Definition emb_pred {E1 E2} (f : {ffun E1 -> E2}) := 
  hom_pred f && [forall e1, forall e2, (f e1 <= f e2) ==> (e1 <= e2)].

Definition emb_rel E1 E2 := ??|{ffun E1 -> E2 | emb_pred}|.

Section Def.
Context {E1 E2 : eventType L}.
Implicit Types (f : {ffun E1 -> E2 | emb_pred}).
Implicit Types (g : {emb E1 -> E2}).

Lemma femb_ca_reflecting f :
  [forall e1, forall e2, (e1 <= e2) == (f e1 <= f e2)].
Proof. 
  case: f=> [{}f] /= /andP[] /andP[] ?.
  move=> /forall2P H1 /forall2P H2.
  apply/forall2P=> e1 e2; apply/eqP/eq_bool_iff.
  split; apply/implyP; [exact/H1 | exact/H2].
Qed.

Lemma emb_pred_of_emb g : 
  emb_pred [ffun x => g x].
Proof. 
  apply/andP; split; first exact/hom_pred_of_hom. 
  apply/forall2P=> e1 e2; rewrite !ffunE.
  by apply/implyP; rewrite (ca_reflecting g).
Qed.

Lemma emb_mixin f : 
  lPoset.Emb.Emb.mixin_of f.
Proof. 
  constructor=> e1 e2.
  move: (femb_ca_reflecting f).
  move=> /fin_ca_reflectingP H. 
  by move: (H e1 e2)=> ->.
Qed.

Definition fhom_of_femb f : 
  {ffun E1 -> E2 | hom_pred} := Sub _ (proj1 (andP (valP f))).

Definition femb_of_emb g : {ffun E1 -> E2 | emb_pred} := 
  Sub [ffun x => g x] (emb_pred_of_emb g).

Definition emb_of_femb f : {emb E1 -> E2} :=
  let base  := lPoset.Hom.Hom.class (hom_of_fhom (fhom_of_femb f)) in
  let mixin := emb_mixin f in 
  lPoset.Emb.Emb.Pack (lPoset.Emb.Emb.Class base mixin).

Definition oemb f : option {emb  E1 -> E2} := 
  omap emb_of_femb (insub [ffun x => f x]).

End Def.

Section Theory.

Lemma fembP E1 E2 :
  reflect ?|{emb E1 -> E2}| ??|{ffun E1 -> E2 | emb_pred}|.
Proof.
  apply/equivP; first exact/fin_inhP.
  apply/(inh_iff emb_of_femb).  
  exact/femb_of_emb.
Qed.

Lemma emb_refl : reflexive emb_rel.
Proof. apply/(is_inh_refl fembP)=> E; exact/[emb of idfun : E -> E]. Qed.

Lemma emb_trans : transitive emb_rel.
Proof. apply/(is_inh_trans fembP)=> ??? f g; exact/[emb of g \o f]. Qed.

End Theory.

End Emb.

Prenex Implicits emb_pred emb_of_femb femb_of_emb oemb.

Section Iso.
Context {L : eqType}.
Implicit Types (E : eventType L).

Definition iso_pred {E1 E2} (f : {ffun E1 -> E2}) := 
  bhom_pred f && [forall e1, forall e2, (f e1 <= f e2) ==> (e1 <= e2)].

Definition iso_rel E1 E2 := ??|{ffun E1 -> E2 | iso_pred}|.

Section Def.
Context {E1 E2 : eventType L}.
Implicit Types (f : {ffun E1 -> E2 | iso_pred}).
Implicit Types (g : {iso E1 -> E2}).

Lemma iso_pred_of_iso g : 
  iso_pred [ffun x => g x].
Proof. 
  apply/andP; split; first exact/bhom_pred_of_bhom. 
  apply/forall2P=> e1 e2; rewrite !ffunE. 
  rewrite (ca_reflecting g); exact/implyP.
Qed.

Lemma emb_pred_of_fiso f : iso_pred f -> emb_pred f. 
Proof. by move=> /andP[] /andP[] /andP[] Hf _ _ Hm; apply/andP. Qed. 

Definition fbhom_of_fiso f : {ffun E1 -> E2 | bhom_pred} := 
  Sub _ (proj1 (andP (valP f))).

Definition femb_of_fiso f : 
  {ffun E1 -> E2 | emb_pred} := Sub _ (emb_pred_of_fiso (valP f)).

Definition fiso_of_iso g : {ffun E1 -> E2 | iso_pred} := 
  Sub [ffun x => g x] (iso_pred_of_iso g).

Definition iso_of_fiso f : {iso E1 -> E2} :=
  let fbhom := fbhom_of_fiso f in
  let base  := lPoset.bHom.bHom.class (bhom_of_fbhom fbhom) in
  let mixin := emb_mixin (femb_of_fiso f) in 
  lPoset.Iso.Iso.Pack (lPoset.Iso.Iso.Class base mixin).

Definition oiso f : option {iso  E1 -> E2} := 
  omap iso_of_fiso (insub [ffun x => f x]).

End Def. 

Section Theory.

Lemma fisoP E1 E2 :
  reflect ?|{iso E1 -> E2}| ??|{ffun E1 -> E2 | iso_pred}|.
Proof.
  apply/equivP; first exact/fin_inhP.
  apply/(inh_iff iso_of_fiso).  
  exact/fiso_of_iso.
Qed.

Lemma iso_refl : reflexive iso_rel.
Proof. apply/(is_inh_refl fisoP)=> E; exact/[iso of idfun : E -> E]. Qed.

Lemma iso_trans : transitive iso_rel.
Proof. apply/(is_inh_trans fisoP)=> ??? f g; exact/[iso of g \o f]. Qed.

End Theory.

Section Build.

Lemma of_ihoms_class {E1 E2} (f : {ihom E1 -> E2}) (g : {ihom E2 -> E1}) : 
  lPoset.Iso.Iso.class_of f.
Proof.
  have bhom_ff : bhom_pred [ffun e => f e].
  - apply/andP; split; [exact/ihom_pred_of_ihom|].
    by apply/leq_card/ihom_inj.
  pose ff := SubFinfunOf bhom_ff.
  suff : lPoset.Iso.Iso.class_of ff.
  - move=> C; pose f' := lPoset.Iso.Iso.Pack C.
    apply/(@lPoset.Iso.Build.of_eqfun_class _ _ _ f').
    by move=> x; rewrite /f' /= ffunE. 
  do 2 constructor.
  - apply/(@lPoset.Hom.Build.of_eqfun_class _ _ _ f).
    by move=> x /=; rewrite ffunE.
  - exact/bhom_mixin.
  by move=> ??; rewrite !ffunE fihom_ca_reflecting.
Qed.

Definition of_ihoms {E1 E2} : 
  {ihom E1 -> E2} -> {ihom E2 -> E1} -> {iso E1 -> E2} := 
    fun f g => lPoset.Iso.Iso.Pack (of_ihoms_class f g).

End Build.

End Iso.

Prenex Implicits iso_pred iso_of_fiso fiso_of_iso oiso.

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
  ({bhom eventType t -> eventType u}) -> ({emb eventType t -> eventType u}) := 
    fun f => lPoset.Iso.Build.of_tot_bij f (@tca_total L n t).

End Def.

End Iso. 

Section HomP. 
Context {L : eqType} {n m : nat} (t : n.-tuple L) (u : m.-tuple L).

Lemma homP :
  reflect ?|{ihom eventType t -> eventType u}| (subseq t u).
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
    have f: ({hom eventType t -> eventType ([tuple] : 0.-tuple L)}).
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
  reflect ?|{iso eventType t -> eventType u}| (t == u :> seq L).
Proof.
  apply/(iffP idP); last first.
  - move=> [f]; move: (lPoset.Iso.Build.inv f)=> g.
    apply/eqP/subseq_anti/andP.
    split; apply/homP; eexists; [exact/f | exact/g].
  move=> /eqP H; have Hn: n = m.
  - by rewrite -(size_tuple t) -(size_tuple u) H.
  move: u H; clear u; case Hn=> u.
  move=> /val_inj ->.
  constructor; exact/[iso of idfun].
Qed.

End IsoP. 

End tPoset.

Export tPoset.tPoset.Exports.
Export tPoset.Theory. 

(* Context (L : Type) (n : nat) (t : n.-tuple L). *)
(* Context (e e1 e2 : tPoset.eventType t). *)
(* Check (lab e : L). *)
(* Check (e1 <= e2 : bool). *)
