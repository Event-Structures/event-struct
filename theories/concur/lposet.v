From RelationAlgebra Require Import lattice monoid rel boolean.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun.
From mathcomp Require Import eqtype choice order seq tuple path.
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

Lemma eq_axiom (f g : E1 -> E2) : f =1 g -> Hom.axiom f -> Hom.axiom g.
Proof. move=> eqf []; split; [exact/(eq_mono1 eqf)| exact/(eq_homo2 eqf)]. Qed.

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

Lemma eq_axiom (f g : E1 -> E2) : f =1 g -> iHom.axiom f -> iHom.axiom g.
Proof. 
  move=> eqf []; split.
  - exact/(eq_mono1 eqf). 
  - exact/(eq_homo2 eqf). 
  exact/(eq_inj _ eqf). 
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

Lemma eq_axiom (f g : E1 -> E2) : f =1 g -> bHom.axiom f -> bHom.axiom g.
Proof. 
  move=> eqf []; split.
  - exact/(eq_mono1 eqf). 
  - exact/(eq_homo2 eqf). 
  exact/(eq_bij _ eqf). 
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

Lemma eq_axiom (f g : E1 -> E2) : f =1 g -> Emb.axiom f -> Emb.axiom g.
Proof. move=> eqf []; split; [exact/(eq_mono1 eqf) | exact/(eq_mono2 eqf)]. Qed.

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

Lemma eq_axiom (f g : E1 -> E2) : f =1 g -> Pref.axiom f -> Pref.axiom g.
Proof. 
  move=> eqf []; split. 
  - exact/(eq_mono1 eqf). 
  - exact/(eq_mono2 eqf). 
  exact/(eq_dw_surj _ eqf).
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

Lemma eq_axiom (f g : E1 -> E2) : f =1 g -> Iso.axiom f -> Iso.axiom g.
Proof. 
  move=> eqf []; split. 
  - exact/(eq_mono1 eqf). 
  - exact/(eq_mono2 eqf). 
  exact/(eq_bij _ eqf).
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

Module Hom.
Section Hom.
Context {L : eqType}. 
Implicit Types (E : eventType L).

Definition axiom {E1 E2} (f : {ffun E1 -> E2}) := 
  [&& [forall e, lab (f e) == lab e]  
    & [forall e1, forall e2, (e1 <= e2) ==> (f e1 <= f e2)]
  ].

Lemma axiomP {E1 E2} (f : {ffun E1 -> E2}) : 
  reflect (lPoset.Hom.Hom.axiom f) (axiom f).
Proof. apply/andPP; [exact/mono1P | exact/homo2P]. Qed.

Definition ohom {E1 E2} f : option {hom E1 -> E2} := 
  let ff := insub [ffun x => f x] : option {ffun E1 -> E2 | axiom} in
  omap (fun f => lPoset.Hom.Hom.Pack (elimT (axiomP (val f)) (valP f))) ff.

Definition hom_le E1 E2 := ??|{ffun E1 -> E2 | axiom}|.

Lemma hom_leP E1 E2 :
  reflect ?|{hom E1 -> E2}| ??|{ffun E1 -> E2 | axiom}|.
Proof.
  apply/equivP; first exact/fin_inhP; apply/inh_iff.
  - move=> [f] /axiomP ax; eexists; exact/ax. 
  move=> [f] fax; exists (finfun f); apply/axiomP.
  apply/(lPoset.Hom.Build.eq_axiom _ fax). 
  by move=> x; rewrite ffunE. 
Qed.

Lemma hom_le_refl : reflexive hom_le.
Proof. apply/(is_inh_refl hom_leP)=> E; exact/[hom of idfun : E -> E]. Qed.

Lemma hom_le_trans : transitive hom_le.
Proof. apply/(is_inh_trans hom_leP)=> ??? f g; exact/[hom of g \o f]. Qed.

End Hom.
End Hom.

Module iHom.
Section iHom.
Context {L : eqType}. 
Implicit Types (E : eventType L).

Definition axiom {E1 E2} (f : {ffun E1 -> E2}) := 
  [&& [forall e, lab (f e) == lab e]  
    , [forall e1, forall e2, (e1 <= e2) ==> (f e1 <= f e2)]
    & injectiveb f
  ].

Lemma axiomP {E1 E2} (f : {ffun E1 -> E2}) : 
  reflect (lPoset.iHom.iHom.axiom f) (axiom f).
Proof. apply/and3PP; [exact/mono1P | exact/homo2P | exact/injectiveP]. Qed.

Definition oihom {E1 E2} f : option {ihom E1 -> E2} := 
  let ff := insub [ffun x => f x] : option {ffun E1 -> E2 | axiom} in
  omap (fun f => lPoset.iHom.iHom.Pack (elimT (axiomP (val f)) (valP f))) ff.

Definition ihom_le E1 E2 := ??|{ffun E1 -> E2 | axiom}|.

Lemma ihom_leP E1 E2 :
  reflect ?|{ihom E1 -> E2}| ??|{ffun E1 -> E2 | axiom}|.
Proof.
  apply/equivP; first exact/fin_inhP; apply/inh_iff.
  - move=> [f] /axiomP ax; eexists; exact/ax. 
  move=> [f] fax; exists (finfun f); apply/axiomP.
  apply/(lPoset.iHom.Build.eq_axiom _ fax). 
  by move=> x; rewrite ffunE. 
Qed.

Lemma ihom_le_refl : reflexive ihom_le.
Proof. apply/(is_inh_refl ihom_leP)=> E; exact/[ihom of idfun : E -> E]. Qed.

Lemma ihom_le_trans : transitive ihom_le.
Proof. apply/(is_inh_trans ihom_leP)=> ??? f g; exact/[ihom of g \o f]. Qed.

End iHom.
End iHom.

Module bHom.

Module Build.
Module Export Exports.
Section Exports.
Context {L : Type} {E1 E2 : eventType L}.
Variable (f : {bhom E1 -> E2}).

Definition bhom_inv := invFh (bhom_bij f).

End Exports.
End Exports.
End Build.

Section bHom.
Context {L : eqType}.
Implicit Types (E : eventType L).

Definition axiom {E1 E2} (f : {ffun E1 -> E2}) := 
  [&& [forall e, lab (f e) == lab e]  
    , [forall e1, forall e2, (e1 <= e2) ==> (f e1 <= f e2)]
    & bijectiveb f
  ].

Lemma axiomP {E1 E2} (f : {ffun E1 -> E2}) : 
  reflect (lPoset.bHom.bHom.axiom f) (axiom f).
Proof. apply/and3PP; [exact/mono1P | exact/homo2P | exact/bijectiveP]. Qed.

Definition obhom {E1 E2} f : option {bhom E1 -> E2} := 
  let ff := insub [ffun x => f x] : option {ffun E1 -> E2 | axiom} in
  omap (fun f => lPoset.bHom.bHom.Pack (elimT (axiomP (val f)) (valP f))) ff.

Definition bhom_le E1 E2 := ??|{ffun E1 -> E2 | axiom}|.

Lemma bhom_leP E1 E2 :
  reflect ?|{bhom E1 -> E2}| ??|{ffun E1 -> E2 | axiom}|.
Proof.
  apply/equivP; first exact/fin_inhP; apply/inh_iff.
  - move=> [f] /axiomP ax; eexists; exact/ax. 
  move=> [f] fax; exists (finfun f); apply/axiomP.
  apply/(lPoset.bHom.Build.eq_axiom _ fax). 
  by move=> x; rewrite ffunE. 
Qed.

Lemma bhom_le_refl : reflexive bhom_le.
Proof. apply/(is_inh_refl bhom_leP)=> E; exact/[bhom of idfun : E -> E]. Qed.

Lemma bhom_le_trans : transitive bhom_le.
Proof. apply/(is_inh_trans bhom_leP)=> ??? f g; exact/[bhom of g \o f]. Qed.

End bHom.
End bHom.

Export bHom.Build.Exports.

Module Emb.
Section Emb.
Context {L : eqType}.
Implicit Types (E : eventType L).

Definition axiom {E1 E2} (f : {ffun E1 -> E2}) := 
  [&& [forall e, lab (f e) == lab e]  
    & [forall e1, forall e2, (f e1 <= f e2) == (e1 <= e2)]
  ].

Lemma axiomP {E1 E2} (f : {ffun E1 -> E2}) : 
  reflect (lPoset.Emb.Emb.axiom f) (axiom f).
Proof. apply/andPP; [exact/mono1P | exact/mono2P]. Qed.

Definition oemb {E1 E2} f : option {emb E1 -> E2} := 
  let ff := insub [ffun x => f x] : option {ffun E1 -> E2 | axiom} in
  omap (fun f => lPoset.Emb.Emb.Pack (elimT (axiomP (val f)) (valP f))) ff.

Definition emb_le E1 E2 := ??|{ffun E1 -> E2 | axiom}|.

Lemma emb_leP E1 E2 :
  reflect ?|{emb E1 -> E2}| ??|{ffun E1 -> E2 | axiom}|.
Proof.
  apply/equivP; first exact/fin_inhP; apply/inh_iff.
  - move=> [f] /axiomP ax; eexists; exact/ax. 
  move=> [f] fax; exists (finfun f); apply/axiomP.
  apply/(lPoset.Emb.Build.eq_axiom _ fax). 
  by move=> x; rewrite ffunE. 
Qed.

Lemma emb_le_refl : reflexive emb_le.
Proof. apply/(is_inh_refl emb_leP)=> E; exact/[emb of idfun : E -> E]. Qed.

Lemma emb_le_trans : transitive emb_le.
Proof. apply/(is_inh_trans emb_leP)=> ??? f g; exact/[emb of g \o f]. Qed.

End Emb.
End Emb.

Module Iso.

Module Build.
Section Build.
Context {L : Type} {E1 E2 : eventType L}.
Variable (f : {iso E1 -> E2}).

Lemma inv_axiom : lPoset.Iso.Iso.axiom (bhom_inv f).
Proof. 
  repeat constructor=> //; last exact/injFh_bij.
  - by move=> e; rewrite -(lab_preserving f) f_invFh. 
  apply/inj_le_homo_mono.
  - exact/bij_inj/injFh_bij.
  - exact/bij_inj/bhom_bij/f.
  - apply/cancel_le_ahomo_homo; first exact/f_invFh.
    exact/mono2aW/(ca_reflecting f).
  exact/(ca_monotone f).
Qed.

End Build.

Module Export Exports.
Section Exports.
Context {L : Type} {E1 E2 : eventType L}.
Variable (f : {iso E1 -> E2}).

Canonical invFh_iso := lPoset.Iso.Iso.Pack (@inv_axiom L E1 E2 f).

End Exports.
End Exports.

End Build.

Export Build.Exports.

Section Iso.
Context {L : eqType}.
Implicit Types (E : eventType L).

Definition axiom {E1 E2} (f : {ffun E1 -> E2}) := 
  [&& [forall e, lab (f e) == lab e]  
    , [forall e1, forall e2, (f e1 <= f e2) == (e1 <= e2)]
    & bijectiveb f
  ].

Lemma axiomP {E1 E2} (f : {ffun E1 -> E2}) : 
  reflect (lPoset.Iso.Iso.axiom f) (axiom f).
Proof. apply/and3PP; [exact/mono1P | exact/mono2P | exact/bijectiveP]. Qed.

Definition oiso {E1 E2} f : option {iso E1 -> E2} := 
  let ff := insub [ffun x => f x] : option {ffun E1 -> E2 | axiom} in
  omap (fun f => lPoset.Iso.Iso.Pack (elimT (axiomP (val f)) (valP f))) ff.

Definition iso_eqv E1 E2 := ??|{ffun E1 -> E2 | axiom}|.

Lemma iso_eqvP E1 E2 :
  reflect ?|{iso E1 -> E2}| ??|{ffun E1 -> E2 | axiom}|.
Proof.
  apply/equivP; first exact/fin_inhP; apply/inh_iff.
  - move=> [f] /axiomP ax; eexists; exact/ax. 
  move=> [f] fax; exists (finfun f); apply/axiomP.
  apply/(lPoset.Iso.Build.eq_axiom _ fax). 
  by move=> x; rewrite ffunE. 
Qed.

Lemma iso_eqv_refl : reflexive iso_eqv.
Proof. apply/(is_inh_refl iso_eqvP)=> E; exact/[iso of idfun : E -> E]. Qed.

Lemma iso_eqv_sym : symmetric iso_eqv.
Proof. 
  apply/(is_inh_sym iso_eqvP)=> ?? f. 
  exact/[iso of bhom_inv f]. 
Qed.

Lemma iso_eqv_trans : transitive iso_eqv.
Proof. apply/(is_inh_trans iso_eqvP)=> ??? f g; exact/[iso of g \o f]. Qed.

End Iso.
End Iso.

End lFinPoset.

Export lFinPoset.lFinPoset.Exports.
Export lFinPoset.bHom.Build.Exports.
Export lFinPoset.Iso.Build.Exports.


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
    + by exists (fun e => match efalse e with end); repeat constructor. 
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
  - move=> [f]; pose g := [iso of bhom_inv f].
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
