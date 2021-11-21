From RelationAlgebra Require Import lattice boolean.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From mathcomp Require Import eqtype choice order finmap fintype.
From eventstruct Require Import utils relalg lposet.

(******************************************************************************)
(* This file provides a theory of prime event structures.                     *)
(* Prime event structure inherits partial causality order from pomset and     *)
(* also has binary conflict relation (symmetric and irreflexive).             *)
(*                                                                            *)
(*       Prime.eventStruct E == the type of prime event structures with       *)
(*                              binary conflict, consisting of                *)
(*                              a causality relation <= (a partial order),    *)
(*                              and a binary conflict relation # (irreflexive *)
(*                              and symmetric).                               *)
(*       Prime.eventType d   == a type of events, i.e. a type equipped with   *)
(*                              prime event structure instance.               *)
(*       Prime.cfg d es x    == a predicate asserting that subset of events x *)
(*                              given as decidable predicate) forms a         *)
(*                              configuration of the event structure es.      *)
(*                              Configuration is a causally-closed and        *)
(*                              conflict-free subset of events.               *)
(*       PrimeG.eventStruct E == the type of prime event structures with      *)
(*                               general conflict, consisting of              *)
(*                               a causality relation <= (a partial order),   *)
(*                               and a general conflict predice gcf over      *)
(*                               finite subset of events.                     *)
(*                               and symmetric).                              *)
(*       PrimeG.eventType d   == a type of events, i.e. a type equipped with  *)
(*                               prime event structure instance.              *)
(*       PrimeG.cfg d es x    == a predicate asserting that subset of events  *)
(*                               x (given as decidable predicate) forms a     *)
(*                               configuration of the event structure es.     *)
(*                               Configuration is a causally-closed and       *)
(*                               conflict-free subset of events.              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.LTheory.
Local Open Scope order_scope.
Local Open Scope fset_scope.

(* a hack to bypass a shadowing problem caused by relation-algebra import *)
Local Notation symmetric  := Coq.ssr.ssrbool.symmetric.
Local Notation transitive := Coq.ssr.ssrbool.transitive.

Declare Scope prime_eventstruct_scope.
Delimit Scope prime_eventstruct_scope with prime_es.
Local Open Scope prime_eventstruct_scope.

Reserved Notation "x \# y" (at level 75, no associativity).

Definition fin_cause {T : eqType} (ca : rel T) :=
  forall e, is_finite (ca^~ e).

Definition hereditary {T : Type} (ca cf : rel T) := 
  forall x y z : T, cf x y -> ca y z -> cf x z.

Module Elem. 

Module Export EventStruct.
Section ClassDef. 

Record mixin_of (E0 : Type) (L : Type) (eb : lPoset.lPoset.class_of E0 L)
                (E := lPoset.lPoset.Pack eb) := Mixin {
  _ : fin_cause (ca : rel E)
}.

Set Primitive Projections.
Record class_of (E : Type) (L : Type) := Class {
  base  : lPoset.lPoset.class_of E L;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> lPoset.lPoset.class_of.

Structure type (L : Type) := Pack { sort; _ : class_of sort L }.

Local Coercion sort : type >-> Sortclass.

Variables (E : Type) (L : Type) (cT : type L).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') L in c.
Definition clone c of phant_id class c := @Pack E c.
(* Definition clone_with disp' c of phant_id class c := @Pack disp' T c. *)

Definition pack :=
  fun bE b & phant_id (@lPoset.lPoset.class L bE) b =>
  fun m => Pack (@Class E L b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @Order.POrder.Pack tt cT class.
Definition lposetType := @lPoset.lPoset.Pack L cT class.
End ClassDef.

Module Export Exports.
Coercion base : class_of >-> lPoset.lPoset.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> Order.POrder.type.
Coercion lposetType : type >-> lPoset.eventType.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical lposetType.
End Exports.

End EventStruct.

Notation eventType := EventStruct.type.
Notation eventStruct := EventStruct.class_of.
Notation EventType E L m := (@EventStruct.pack E L _ _ id m).

Module Export Theory.
Section Theory.

Context {L : Type} {E : eventType L}.
Implicit Types (e : E).

Lemma prefix_fin (e : E) : is_finite (<= e).
Proof. by move: e; case: E => ? [? []]. Qed.

(* TODO: move to pomset? *)
Lemma prefix_ca_closed (e : E) : ca_closed (<= e).
Proof. move=> e1 e2 /=; exact: le_trans. Qed.

End Theory.
End Theory.

End Elem.

Export Elem.EventStruct.Exports.
Export Elem.Theory.

Module PrimeC.

Module EventStruct.
Section ClassDef.

Record mixin_of (E0 : Type) (L : Type) (b : Elem.EventStruct.class_of E0 L)
                (E := Elem.EventStruct.Pack b) := Mixin {
  cons : pred {fset E};

  _ : forall (e : E), cons [fset e];
  _ : forall (X Y : {fset E}), X `<=` Y -> cons Y -> cons X;
  _ : forall X e e', e <= e' -> cons (e' |` X) -> cons (e |` X)
}.

Set Primitive Projections.
Record class_of (E L : Type) := Class {
  base  : Elem.EventStruct.class_of E L;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Elem.EventStruct.class_of.

Structure type (L : Type) := Pack { sort; _ : class_of sort L }.

Local Coercion sort : type >-> Sortclass.

Variables (E : Type) (L : Type) (cT : type L).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') L in c.
Definition clone c of phant_id class c := @Pack E L c.
(* Definition clone_with disp' c of phant_id class c := @Pack disp' T c. *)

Definition pack :=
  fun bE b & phant_id (@Elem.EventStruct.class L bE) b =>
  fun m => Pack (@Class E L b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @Order.POrder.Pack tt cT class.
Definition lposetType := @lPoset.lPoset.Pack L cT class.
Definition elemEventType := @Elem.EventStruct.Pack L cT class.
End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Elem.EventStruct.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> Order.POrder.type.
Coercion lposetType : type >-> lPoset.eventType.
Coercion elemEventType : type >-> Elem.eventType.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical lposetType.
Canonical elemEventType.
End Exports.


End EventStruct.

Export EventStruct.Exports.

Notation eventType := EventStruct.type.
Notation eventStruct := EventStruct.class_of.
Notation EventType E L m := (@EventStruct.pack E L _ _ id m).

Section Def.

Variable (L : Type) (E : eventType L).

Definition cons : pred {fset E} :=
  EventStruct.cons (EventStruct.class E).

Definition cf_free (p : pred E) := 
  forall (s : {fset E}), {subset s <= p} -> cons s.

Definition cfg (p : pred E) := ca_closed p /\ cf_free p.

End Def.

Prenex Implicits cons.

Module Export Syntax.
Notation cons := cons (only parsing).
End Syntax.

Module Export Theory.
Section Theory.

Context {L : Type} {E : eventType L}.

Lemma cons_self (e : E) : cons [fset e].
Proof. by move: e; case: E => ? [? []]. Qed.

Lemma cons_contr (X Y : {fset E}) : X `<=` Y -> cons Y -> cons X.
Proof. by move: X Y; case: E => ? [? []]. Qed.

Lemma cons_prop X (e1 e2 : E) : 
  e1 <= e2 -> cons (e2 |` X) -> cons (e1 |` X).
Proof. by move: X e1 e2; case: E => ? [? []]. Qed.

Lemma cons_ca_contr (X Y : {fset E}) :
  {subsumes X <= Y : x y / x <= y} -> cons Y -> cons X.
Proof.
  move: X {2}(X `\` Y) (erefl (X `\` Y))=> /[swap].
  elim/fset_ind=> [?/eqP/[! fsetD_eq0]/cons_contr//|].
  move=> x ?? IHxy X XYE /[dup] S + cY; rewrite -(@fsetD1K _ x X); last first.
  - move/fsetP/(_ x): XYE; rewrite ?inE eqxx andbC /=; by case: (x \in X).
  case/(_ x)=> [/[! (inE, eqxx)]//|y ? /cons_prop]; apply.
  apply: IHxy=> // [|?]; last first.
  - rewrite ?inE=> /orP[/eqP->|/andP[_ /S //]]; by exists y.
  rewrite fsetDUl fsetDDl [x |` _]fsetUC -fsetDDl XYE fsetDUl.
  have/eqP->: ([fset y] `\` Y == fset0) by rewrite fsetD_eq0 fsub1set.
  by rewrite fsetDv ?fset0U mem_fsetD1.
Qed.

Lemma prefix_cf_free (e : E) : cf_free (<= e).
Proof. 
  move=> X S; apply/(@cons_ca_contr _ [fset e])/cons_self.
  move=> x i; exists e; rewrite ?inE //; exact/S.
Qed.

Lemma prefix_cfg (e : E) : cfg (<= e).
Proof. split; [exact/prefix_ca_closed | exact/prefix_cf_free]. Qed.

End Theory.
End Theory.

Module Export Hom.

Module Hom.
Section ClassDef. 

(* TODO: homomorphism between pomsets labelled by different labels? *)
Context {L : Type} (E1 E2 : PrimeC.eventType L).
Implicit Types (f : E1 -> E2).

Record mixin_of f := Mixin {
  _ : forall X : {fset E1}, cons X -> cons (f @` X)
}.

Set Primitive Projections.
Record class_of f := Class {
  base  : lPoset.Hom.Hom.class_of f;
  mixin : mixin_of f;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> lPoset.Hom.Hom.class_of.

Structure type := Pack { apply ; _ : class_of apply }.

Local Coercion apply : type >-> Funclass.

Variables (cT : type).

Definition class := let: Pack _ c as cT' := cT return class_of (apply cT') in c.
Definition clone f c of phant_id class c := @Pack f c.

Definition homType := lPoset.Hom.Hom.Pack class.

Definition mk h mkH : type :=
  mkH (let: Pack _ c := h return @class_of h in c).

Definition type_of (_ : phant (E1 -> E2)) := type.

(* Definition pack := *)
(*   fun bE b & phant_id (@Order.POrder.class tt bE) b => *)
(*   fun m => Pack (@Class E L b m). *)

End ClassDef.

Module Export Exports.
Coercion mixin : class_of >-> mixin_of.
Coercion apply : type >-> Funclass.
Coercion homType : type >-> lPoset.Hom.Hom.type.
Canonical homType.
End Exports.

End Hom.

Export Hom.Exports.

Module Export Syntax. 
Notation hom := Hom.type.
Notation "{ 'hom' T }" := (@Hom.type_of _ _ _ (Phant T)) : prime_eventstruct_scope.
Notation "[ 'hom' 'of' f ]" := 
  (Hom.mk (fun hCls => @Hom.Pack _ _ _ f hCls))
  (at level 0, format "[ 'hom'  'of'  f ]") : prime_eventstruct_scope.
End Syntax. 

Module Export Theory.
Section Theory. 
Context {L : Type} {E1 E2 : eventType L} (f : {hom E1 -> E2}).

Lemma cons_mon (X : {fset E1}) : 
  cons X -> cons (f @` X).
Proof.
  by case: f => ? [[[??[]]]]; apply.
Qed.

Lemma hom_cf_free (C1 : pred E1) (C2 : pred E2) : 
  (forall x, C2 x <-> exists2 y, C1 y & x = f y) ->
  cf_free C1 -> cf_free C2.
Proof.
  move=> CE cf s S.
  suff[?<-?]: exists2 s' : {fset E1}, f @` s' = s & {subset s' <= C1}.
  - exact/cons_mon/cf.
  elim/fset_ind: s S=> [_| x s ni IHs].
  - exists fset0=> //.
    apply/fsetP=> ?; apply/imfsetP=> /= [[?]]; by rewrite ?inE.
  move=> S; case: IHs=> [? /(fsubsetP (fsubsetU1 x _))/S //|].
  case: (CE x)=> [[]]; first by apply/S; rewrite ?inE eqxx.
  move=> y ? -> _ s' <- S'; exists (y |` s').
  - apply/fsetP=> z; apply/imfsetP=> /=; rewrite ?inE.
    case: (z =P f y)=> /= [->|?]; first by (exists y; rewrite ?inE ?eqxx).
    case: ifP=> [/imfsetP/= [w I->]|]; first by exists w; rewrite ?inE ?I.
    move=> /imfsetP/= F [w /[! inE]/orP[/eqP->//|*]]; apply F; by exists w.
  by move=> ?; rewrite ?inE=> /orP[/eqP->|/S'].
Qed.

Lemma hom_cf_free_fset (C : {fset E1}) :
  cf_free (mem C) -> cf_free (mem (f @` C)).
Proof. apply/hom_cf_free=> ?; split=> I; exact/imfsetP/I. Qed.

End Theory.
End Theory.

Module Build.
Section Build.
Context {L : Type}.
Implicit Types (E : eventType L).

Definition mk_hom {E1 E2 : eventType L} h mkH : {hom E1 -> E2} :=
  mkH (let: Hom.Pack _ c := h return @Hom.class_of L E1 E2 h in c).

Lemma id_class {E} : Hom.class_of (@idfun E).
Proof.
  by (do 2 split)=> // ?; rewrite imfset_id.
Qed.

Lemma comp_class {E1 E2 E3} (f : {hom E2 -> E3}) (g : {hom E1 -> E2}) : 
  Hom.class_of (comp f g).
Proof. 
  (do 2 split); first apply lPoset.Hom.Build.comp_class.
  move=> ?. by rewrite imfset_comp=> /cons_mon/cons_mon.
Qed.

Lemma of_eqfun_class {E1 E2} (f : {hom E1 -> E2}) g : 
  g =1 f -> Hom.class_of g.
Proof. 
  move=> H; (repeat constructor); move=> ?.
  - rewrite !H; exact/lab_preserving.
  move=> ?; rewrite !H; exact/ca_monotone.
  move/(cons_mon f); by rewrite -(eq_imfset _ H (fun=> erefl)).
Qed.

Definition of_eqfun {E1 E2} (f : {hom E1 -> E2}) g : g =1 f -> {hom E1 -> E2} := 
  fun eqf => Hom.Pack (of_eqfun_class eqf).

End Build.

Module Export Exports.
Section Exports.
Context {L : Type}.
Implicit Types (E : eventType L).

Canonical id_hom E : {hom E -> E} := Hom.Pack id_class.

Canonical comp_hom E1 E2 E3 : {hom E2 -> E3} -> {hom E1 -> E2} -> {hom E1 -> E3} :=
  fun f g => Hom.Pack (comp_class f g).

End Exports.
End Exports.
End Build.

End Hom.

Module Export Emb.

Import lPoset.Emb.Syntax.

Module Emb.
Section ClassDef. 

Context {L : Type} (E1 E2 : PrimeC.eventType L).
Implicit Types (f : E1 -> E2).

Record mixin_of f := Mixin {
  _ : forall e1 e2, f e1 <= f e2 -> e1 <= e2;
  _ : forall X : {fset E1}, cons (f @` X) -> cons X
}.

Set Primitive Projections.
Record class_of f := Class {
  base  : PrimeC.Hom.Hom.class_of f; 
  mixin : mixin_of f;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> PrimeC.Hom.Hom.class_of.

Structure type := Pack { apply ; _ : class_of apply }.

Local Coercion apply : type >-> Funclass.

Variables (cT : type).

Definition class := let: Pack _ c as cT' := cT return class_of (apply cT') in c.
Definition clone f c of phant_id class c := @Pack f c.

(* Definition pack := *)
(*   fun bE b & phant_id (@Order.POrder.class tt bE) b => *)
(*   fun m => Pack (@Class E L b m). *)

Definition homType := PrimeC.Hom.Hom.Pack class.

Definition mk h mkH : type :=
  mkH (let: Pack _ c := h return @class_of h in c).

Definition type_of (_ : phant (E1 -> E2)) := type.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> PrimeC.Hom.Hom.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion apply : type >-> Funclass.
Coercion homType : type >-> PrimeC.Hom.Hom.type.
Canonical homType.
End Exports.

End Emb.

Export Emb.Exports.

Module Export Syntax. 
Notation emb := Emb.type.
Notation "{ 'emb' T }" := (@Emb.type_of _ _ _ (Phant T)) : prime_eventstruct_scope.
Notation "[ 'emb' 'of' f ]" := 
  (Emb.mk (fun hCls => @Emb.Pack _ _ _ f hCls))
  (at level 0, format "[ 'emb'  'of'  f ]") : prime_eventstruct_scope.
End Syntax. 

Module Export Theory.
Section Theory. 
Context {L : Type} {E1 E2 : eventType L} (f : {emb E1 -> E2}).

Lemma cons_antimon (X : {fset E1}) : 
  cons (f @` X) -> cons X.
Proof.
  case: f => ? [?[?]]; exact.
Qed.

Lemma emb_cf_free (C1 : pred E1) (C2 : pred E2) : 
  (forall x, C2 x <-> exists2 y, C1 y & x = f y) ->
  cf_free C1 <-> cf_free C2.
Proof.
  move=> CE; split=> [/(hom_cf_free CE) //| cf s S].
  apply/cons_antimon/cf=> ? /imfsetP[y /S ? ->].
  by apply/CE; exists y.
Qed.

End Theory.
End Theory.

Module TolPosetEmb.
Section TolPosetEmb.

Context {L : Type} {E1 E2 : eventType L} (f : {emb  E1 -> E2}).

Definition class : lPoset.Emb.Emb.class_of f.
case f=> ? [[??] [?]]; by do ? split=> //.
Qed.

End TolPosetEmb.

Module Exports.

Canonical lposet_emb_of_prime_es {L : Type} {E1 E2 : eventType L} (f : {emb  E1 -> E2}) 
  := lPoset.Emb.Emb.Pack (class f).

End Exports.


End TolPosetEmb.

Import TolPosetEmb.Exports.

Module Build.
Section Build.
Context {L : Type}.
Implicit Types (E : eventType L).

Lemma id_class {E} : Emb.class_of (@idfun E).
Proof. 
  split=> //; first exact/Hom.Build.id_class.
  by split=> // ?; rewrite imfset_id.
Qed.

(* Lemma comp_mixin {E1 E2 E3} (f : {emb  E1 -> E2}) (g : {emb E2 -> E3}) : 
  Emb.mixin_of (g \o f).
Proof. 
  split=> //. apply/Hom.Build.comp_mixin.
  by constructor=> ??; rewrite -(ca_reflecting f) -(ca_reflecting g). Qed. *)

Lemma comp_class {E1 E2 E3} (f : {emb  E2 -> E3}) (g : {emb E1 -> E2}) : 
  Emb.class_of (f \o g).
Proof. 
  split=> //; first exact/Hom.Build.comp_class; split.
  - by case: (lPoset.Emb.Build.comp_mixin [emb of g]%pomset [emb of f]%pomset).
  by move=> ?; rewrite imfset_comp=> /cons_antimon/cons_antimon.
Qed.

Lemma of_eqfun_class {E1 E2} (f : {emb  E1 -> E2}) g :
  g =1 f -> Emb.class_of g.
Proof.
  move=> E; split=> //; first exact/Hom.Build.of_eqfun_class; split.
  - by case: (lPoset.Emb.Build.of_eqfun_class E)=> ? [].
  by move=> X; rewrite (eq_imfset _ E (fun=> erefl))=> /cons_antimon.
Qed.

Definition of_eqfun {E1 E2} (f : {emb  E1 -> E2}) g : g =1 f -> {emb  E1 -> E2} := 
  fun eqf => Emb.Pack (of_eqfun_class eqf).

End Build.
Module Export Exports.
Section Exports.
Context {L : Type}.
Implicit Types (E : eventType L).

Canonical id_emb E : {emb E -> E} := Emb.Pack id_class.

Canonical comp_emb E1 E2 E3 : {emb E2 -> E3} -> {emb E1 -> E2} -> {emb E1 -> E3} :=
  fun f g => Emb.Pack (comp_class f g).

End Exports.
End Exports.
End Build.
End Emb.

Module Export Pref.

Import lPoset.Pref.Syntax.

Module Pref.
Section ClassDef. 

Context {L : Type} (E1 E2 : PrimeC.eventType L).
Implicit Types (f : E1 -> E2).

Record mixin_of f := Mixin {
  _ : forall e1 e2, e1 <= f e2 -> exists e, f e = e1;
}.

Set Primitive Projections.
Record class_of f := Class {
  base  : Emb.class_of f; 
  mixin : mixin_of f;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Emb.class_of.

Structure type := Pack { apply ; _ : class_of apply }.

Local Coercion apply : type >-> Funclass.

Variables (cT : type).

Definition class := let: Pack _ c as cT' := cT return class_of (apply cT') in c.
Definition clone f c of phant_id class c := @Pack f c.

(* Definition pack := *)
(*   fun bE b & phant_id (@Order.POrder.class tt bE) b => *)
(*   fun m => Pack (@Class E L b m). *)

Definition homType  := Hom.Pack class.
Definition embType  := Emb.Pack class.

Definition mk h mkH : type :=
  mkH (let: Pack _ c := h return @class_of h in c).

Definition type_of (_ : phant (E1 -> E2)) := type.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Emb.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion apply : type >-> Funclass.
Coercion homType : type >-> Hom.type.
Coercion embType : type >-> Emb.type.
Canonical embType.
Canonical homType.
End Exports.

End Pref.

Export Pref.Exports.

Module Export Syntax. 
Notation pref := Pref.type.
Notation "{ 'pref' T }" := (@Pref.type_of _ _ _ (Phant T)) : prime_eventstruct_scope.
Notation "[ 'pref' 'of' f ]" := 
  (Pref.mk (fun hCls => @Pref.Pack _ _ _ f hCls))
  (at level 0, format "[ 'pref'  'of'  f ]") : prime_eventstruct_scope.
End Syntax.

Module TolPosetPref.
Section TolPosetPref.

Context {L : Type} {E1 E2 : eventType L} (f : {pref  E1 -> E2}).

Definition class : lPoset.Pref.Pref.class_of f.
case f=> ? [b []]; split=> //=; exact/(TolPosetEmb.class (Emb.Emb.Pack b)).
Qed.

End TolPosetPref.

Module Exports.

Canonical lposet_pref_of_prime_es {L : Type} {E1 E2 : eventType L} (f : {pref  E1 -> E2}) 
  := lPoset.Pref.Pref.Pack (class f).

End Exports.

End TolPosetPref.

Import TolPosetPref.Exports.


Module Export Theory.
Section Theory. 
Context {L : Type} {E1 E2 : eventType L} (f : {pref E1 -> E2}).


Lemma pref_cfg (C1 : pred E1) (C2 : pred E2) : 
  (forall e, C2 e <-> exists2 e', C1 e' & e = f e') ->
  cfg C1 <-> cfg C2.
Proof.
  move=> CE; by rewrite /cfg (pref_ca_closed CE) (emb_cf_free CE). 
Qed.

Lemma pref_ca_closed_fset (C1 : {fset E1}) : 
  ca_closed (mem C1) <-> ca_closed (mem (f @` C1)%fset).
Proof. apply/pref_ca_closed=> ?; split=> I; exact/imfsetP/I. Qed.

End Theory.
End Theory.

Module Build.
Section Build.
Context {L : Type}.
Implicit Types (E : eventType L).

Lemma id_class {E} : Pref.class_of (@idfun E).
Proof. 
  split=> //; first exact/Emb.Build.id_class.
  by case : (@lPoset.Pref.Build.id_class L E)=> ? [].
Qed.

Lemma comp_class {E1 E2 E3} (f : {pref E2 -> E3}) (g : {pref E1 -> E2}) : 
  Pref.class_of (f \o g).
Proof. 
  split=> //; first exact/Emb.Build.comp_class.
  by case : (lPoset.Pref.Build.comp_mixin [pref of g]%pomset [pref of f]%pomset).
Qed.

Lemma of_eqfun_class {E1 E2} (f : {pref  E1 -> E2}) g :
  g =1 f -> Pref.class_of g.
Proof.
  move=> E; split=> //; first exact/Emb.Build.of_eqfun_class.
  by case : (lPoset.Pref.Build.of_eqfun_class E)=> ? [].
Qed.

Definition of_eqfun {E1 E2} (f : {pref  E1 -> E2}) g : g =1 f -> {pref  E1 -> E2} := 
  fun eqf => Pref.Pack (of_eqfun_class eqf).

End Build.
Module Export Exports.
Section Exports.
Context {L : Type}.
Implicit Types (E : eventType L).

Canonical id_pref E : {pref E -> E} := Pref.Pack id_class.

Canonical comp_pref E1 E2 E3 : {pref E2 -> E3} -> {pref E1 -> E2} -> {pref E1 -> E3} :=
  fun f g => Pref.Pack (comp_class f g).

End Exports.
End Exports.
End Build.
End Pref.

Module Export bHom.

Import lPoset.bHom.Syntax.

Module bHom.
Section ClassDef. 

Context {L : Type} (E1 E2 : PrimeC.eventType L).
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

Definition mk h mkH : type :=
  mkH (let: Pack _ c := h return @class_of h in c).

Definition type_of (_ : phant (E1 -> E2)) := type.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Hom.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion apply : type >-> Funclass.
Coercion homType : type >-> Hom.type.
Canonical homType.
End Exports.

End bHom.

Export bHom.Exports.

Module Export Syntax. 
Notation bhom := bHom.type.
Notation "{ 'bhom' T }" := (@bHom.type_of _ _ _ (Phant T)) : prime_eventstruct_scope.
Notation "[ 'bhom' 'of' f ]" := 
  (bHom.mk (fun hCls => @bHom.Pack _ _ _ f hCls))
  (at level 0, format "[ 'bhom'  'of'  f ]") : prime_eventstruct_scope.
End Syntax.

Module TolPosetbHom.
Section TolPosetbHom.

Context {L : Type} {E1 E2 : PrimeC.eventType L} (f : {bhom E1 -> E2}).

Definition class : lPoset.bHom.bHom.class_of f.
case f=> ? [[??] [g *]]; by split=> //; exists g.
Defined.


End TolPosetbHom.

Module Exports.

Canonical lposet_bhom_of_prime_es {L : Type} {E1 E2 : PrimeC.eventType L} (f : {bhom  E1 -> E2}) 
  := lPoset.bHom.bHom.Pack (class f).

End Exports.

End TolPosetbHom.

Import TolPosetbHom.Exports.

Module Build.
Section Build.
Context {L : Type}.
Implicit Types (E : eventType L).

Lemma id_class {E} : bHom.class_of (@idfun E).
Proof. 
  split=> //; first exact/Hom.Build.id_class.
  by exists id.
Qed.

Lemma comp_class {E1 E2 E3} (f : {bhom  E2 -> E3}) (g : {bhom E1 -> E2}) :
  bHom.class_of (f \o g).
Proof.
  split=> //; first exact/Hom.Build.comp_class.
  case: (lPoset.bHom.Build.comp_class [bhom of f]%pomset [bhom of g]%pomset)=> ? [h *].
  by exists h.
Qed.

Lemma of_eqfun_class {E1 E2} (f : {bhom  E1 -> E2}) g : 
  g =1 f -> bHom.class_of g.
Proof.
  move=> E; split=> //; first exact/Hom.Build.of_eqfun_class.
  case : (lPoset.bHom.Build.of_eqfun_class E)=> ? [h *].
  by exists h.
Qed.

Definition of_eqfun {E1 E2} (f : {bhom  E1 -> E2}) g : g =1 f -> {bhom  E1 -> E2} := 
  fun eqf => bHom.Pack (of_eqfun_class eqf).

End Build.
Module Export Exports.
Section Exports.
Context {L : Type}.
Implicit Types (E : eventType L).

Canonical id_bhom E : {bhom E -> E} := bHom.Pack id_class.

Canonical comp_bhom E1 E2 E3 : {bhom E2 -> E3} -> {bhom E1 -> E2} -> {bhom E1 -> E3} :=
  fun f g => bHom.Pack (comp_class f g).

End Exports.
End Exports.
End Build.
End bHom.

Module Export Iso.

Module Iso.
Section ClassDef. 

Context {L : Type} (E1 E2 : PrimeC.eventType L).
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

Lemma prefMixin : Pref.mixin_of cT.
Proof.
  split=> e1*; case: cT=> f [[? [g *]]].
  by exists (g e1).
Qed.

Definition prefType := Pref.Pack (Pref.Class (Emb.Class class (mixin class)) prefMixin).

Definition mk h mkH : type :=
  mkH (let: Pack _ c := h return @class_of h in c).

Definition type_of (_ : phant (E1 -> E2)) := type.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> bHom.class_of.
Coercion mixin : class_of >-> Emb.mixin_of.
Coercion apply : type >-> Funclass.
Coercion homType  : type >-> Hom.type.
Coercion bhomType : type >-> bHom.type.
Coercion embType  : type >-> Emb.type.
Coercion prefType  : type >-> Pref.type.
Canonical homType.
Canonical bhomType.
Canonical embType.
End Exports.

End Iso.

Export Iso.Exports.

Module Export Syntax. 
Notation iso := Iso.type.
Notation "{ 'iso' T }" := (@Iso.type_of _ _ _ (Phant T)) : prime_eventstruct_scope.
Notation "[ 'iso' 'of' f ]" := 
  (Iso.mk (fun hCls => @Iso.Pack _ _ _ f hCls))
  (at level 0, format "[ 'iso'  'of'  f ]") : prime_eventstruct_scope.
End Syntax.

Module TolPosetIso.
Section TolPosetIso.

Context {L : Type} {E1 E2 : PrimeC.eventType L} (f : {iso E1 -> E2}).

Definition class : lPoset.Iso.Iso.class_of f.
split; [apply/bHom.TolPosetbHom.class|apply/Emb.TolPosetEmb.class].
Defined.

End TolPosetIso.

Module Exports.

Canonical lposet_iso_of_prime_es {L : Type} {E1 E2 : PrimeC.eventType L} (f : {iso  E1 -> E2}) 
  := lPoset.Iso.Iso.Pack (class f).

End Exports.

End TolPosetIso.

Import TolPosetIso.Exports.
Import lPoset.Iso.Syntax.
Import lPoset.bHom.Syntax.
Import TolPosetbHom.Exports.

Module Export Theory.
Section Theory.

Context {L : Type} {E1 E2 : PrimeC.eventType L} (f : {iso E1 -> E2}).

Definition invF := lPoset.bHom.invF ([iso of f]%pomset).

Lemma can_inv : cancel invF f.
Proof. exact/can_inv. Qed.

Lemma inv_can : cancel f invF.
Proof. exact/inv_can. Qed.

End Theory.
End Theory.


Module Build.
Section Build.
Context {L : Type}.
Implicit Types (E : eventType L).

Lemma id_class {E} : Iso.class_of (@idfun E).
Proof.
  split; first exact/bHom.Build.id_class.
  exact/Emb.Build.id_class.
Qed.

Lemma inv_class {E1 E2} (f : {iso E1 -> E2}) :
  Iso.class_of (invF f).
Proof.
  case: (lPoset.Iso.Build.inv_class [iso of f]%pomset)=> [[[[??[g ??[?]]]]]].
  do ? split=> //; [|by exists g|].
  - move=> ??; apply/(@cons_antimon _ _ _ f); rewrite -imfset_comp.
    under eq_imfset do [rewrite /= can_inv|by []]; by rewrite /= imfset_id.
  move=> ? /(@cons_mon _ _ _ f); rewrite -imfset_comp.
  under eq_imfset do [rewrite /= can_inv|by []]; by rewrite /= imfset_id.
Qed.

Definition inv {E1 E2} : {iso E1 -> E2} -> {iso E2 -> E1} := 
  fun f => Iso.Pack (inv_class f).

Lemma comp_class {E1 E2 E3} (f : {iso E2 -> E3}) (g : {iso E1 -> E2}) : 
  Iso.class_of (f \o g).
Proof.
  split; first exact/bHom.Build.comp_class.
  by case: (Emb.Build.comp_class f g).
Qed.

Lemma of_eqfun_class {E1 E2} (f : {iso  E1 -> E2}) g :
  g =1 f -> Iso.class_of g.
Proof.
  move=> E; split; first exact/(bHom.Build.of_eqfun_class E).
  by case: (Emb.Build.of_eqfun_class E).
Qed.

Definition of_eqfun {E1 E2} (f : {iso  E1 -> E2}) g : g =1 f -> {iso  E1 -> E2} := 
  fun eqf => Iso.Pack (of_eqfun_class eqf).

Lemma of_homs_class {E1 E2} (f : {hom  E1 -> E2}) (g : {hom E2 -> E1}) : 
  cancel f g -> cancel g f -> Iso.class_of f.
Proof.
  move=> c c'.
  case: (lPoset.Iso.Build.of_homs_class c c')=> [[[[??[???[?]]]]]].
  do ? split=> //; [by move=> ? /cons_mon|by exists g|].
  move=> ? /(cons_mon g); rewrite -imfset_comp.
  under eq_imfset do [rewrite /= c|by []]; by rewrite imfset_id.
Defined.

Definition of_homs {E1 E2} (f : {hom  E1 -> E2}) (g : {hom E2 -> E1}) : 
  cancel f g -> cancel g f -> ({iso  E1 -> E2}) := 
    fun HK HK' => Iso.Pack (of_homs_class HK HK').

Lemma of_homs_invE {E1 E2} (f : {hom  E1 -> E2}) (g : {hom E2 -> E1}) 
                   (K : cancel f g) (K' : cancel g f) : 
   invF (of_homs K K') = g.
Proof. by []. Qed.

(* Now we can make of_homs_class opaque *)
Global Opaque of_homs_class TolPosetIso.class TolPosetbHom.class.

End Build.
Module Export Exports.
Section Exports.
Context {L : Type}.
Implicit Types (E : eventType L).

Canonical id_iso E : {iso E -> E} := Iso.Pack id_class.

Canonical comp_iso E1 E2 E3 : {iso E2 -> E3} -> {iso E1 -> E2} -> {iso E1 -> E3} :=
  fun f g => Iso.Pack (comp_class f g).

Canonical inv.

End Exports.
End Exports.

End Build.

End Iso.

End PrimeC.

Export PrimeC.EventStruct.Exports.
Export PrimeC.Theory.
Export PrimeC.Syntax.

Export PrimeC.Hom.Build.Exports.
Export PrimeC.Hom.Hom.Exports.
Export PrimeC.Hom.Theory.
Export PrimeC.Emb.Build.Exports.
Export PrimeC.Emb.Emb.Exports.
Export PrimeC.Emb.TolPosetEmb.Exports.
Export PrimeC.Pref.Build.Exports.
Export PrimeC.Pref.Pref.Exports.
Export PrimeC.Pref.Theory.
Export PrimeC.Pref.TolPosetPref.Exports.
Export PrimeC.bHom.Build.Exports.
Export PrimeC.bHom.bHom.Exports.
Export PrimeC.bHom.TolPosetbHom.Exports.
Export PrimeC.Iso.Build.Exports.
Export PrimeC.Iso.Iso.Exports.
Export PrimeC.Iso.Theory.
Export PrimeC.Iso.TolPosetIso.Exports.

Import PrimeC.Hom.Syntax.
Import PrimeC.bHom.Syntax.
Import PrimeC.Emb.Syntax.
Import PrimeC.Pref.Syntax.
Import PrimeC.Iso.Syntax.
Import PrimeC.Syntax.

Module PrimeG.

Module EventStruct.
Section ClassDef.

Record mixin_of (E0 : Type) (L : Type) (b : Elem.EventStruct.class_of E0 L)
                (E := lPoset.lPoset.Pack b) := Mixin {
  gcf : pred {fset E};

  _ : forall (e : E), ~~ (gcf [fset e]);
  _ : forall (X Y : {fset E}), X `<=` Y -> gcf X -> gcf Y;
  _ : forall X e e', e <= e' -> gcf (e |` X) -> gcf (e' |` X)
}.

Set Primitive Projections.
Record class_of (E : Type) (L : Type) := Class {
  base  : Elem.EventStruct.class_of E L;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Elem.EventStruct.class_of.

Structure type (L : Type) := Pack { sort; _ : class_of sort L }.

Local Coercion sort : type >-> Sortclass.

Variables (E : Type) (L : Type) (cT : type L).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') L in c.
Definition clone c of phant_id class c := @Pack E L c.
(* Definition clone_with disp' c of phant_id class c := @Pack disp' T c. *)

Definition pack :=
  fun bE b & phant_id (@Elem.EventStruct.class L bE) b =>
  fun m => Pack (@Class E L b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @Order.POrder.Pack tt cT class.
Definition lposetType := @lPoset.lPoset.Pack L cT class.
Definition elemEventType := @Elem.EventStruct.Pack L cT class.
End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Elem.EventStruct.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> Order.POrder.type.
Coercion lposetType : type >-> lPoset.eventType.
Coercion elemEventType : type >-> Elem.eventType.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical lposetType.
Canonical elemEventType.
End Exports.

End EventStruct.

Export EventStruct.Exports.

Notation eventType := EventStruct.type.
Notation eventStruct := EventStruct.class_of.
Notation EventType E L m := (@EventStruct.pack E L _ _ id m).

Section Def.

Variable (L : Type) (E : eventType L).

Definition gcf : pred {fset E} :=
  EventStruct.gcf (EventStruct.class E).

Definition cf_free (p : pred E) := 
  forall (s : {fset E}), {subset s <= p} -> ~~ gcf s.

Definition cfg (x : pred E) := 
  ca_closed x /\ cf_free x.

End Def.

Prenex Implicits gcf.

Module Import Theory.
Section Theory.

Context {L : Type} {E : eventType L}.

Lemma gcf_self : forall (e : E), ~~ (gcf [fset e]).
Proof. by case: E => ? [? []]. Qed.

Lemma gcf_ext : forall (X Y : {fset E}), X `<=` Y -> gcf X -> gcf Y.
Proof. by case: E => ? [? []]. Qed.

Lemma gcf_hered :
  forall X (e e' : E), e <= e' -> gcf (e |` X) -> gcf (e' |` X).
Proof. by case: E => ? [? []]. Qed.

End Theory.
End Theory.

Module OfPrimeC.
Section OfPrimeC.

Context {L : Type} {E : PrimeC.eventType L}.

Definition gcf : pred {fset E} :=
  fun X => ~~ (cons X).

Lemma gcf_self (e : E) : ~~ gcf [fset e].
Proof. by rewrite /gcf cons_self. Qed.

Lemma gcf_ext (X Y : {fset E}) : X `<=` Y -> gcf X -> gcf Y.
Proof. rewrite /gcf=> H. apply: contraNN. exact: cons_contr. Qed.

Lemma gcf_hered (X : {fset E}) (e e' : E) :
  e <= e' -> gcf (e |` X) -> gcf (e' |` X).
Proof. rewrite /gcf=> H. apply: contraNN. exact: cons_prop. Qed.

Definition cons_gcfMixin := 
  @PrimeG.EventStruct.Mixin E L _ gcf gcf_self gcf_ext gcf_hered.

Definition primeC_primeG := PrimeG.EventType E L cons_gcfMixin.

Lemma cfgE (p : pred E): 
  PrimeC.cfg p <-> 
  @ca_closed L primeC_primeG p /\ @PrimeG.cf_free L primeC_primeG p.
Proof.
  split; move=> [? CF]; split=> // ?/CF; by rewrite /PrimeG.gcf /= /gcf negbK.
Qed.

End OfPrimeC.

Module Export Exports.
Coercion primeC_primeG : PrimeC.eventType >-> PrimeG.eventType.
Canonical primeC_primeG.
End Exports.

End OfPrimeC.


Module ToPrimeC.
Section ToPrimeC.

Context {L : Type} {E : PrimeG.eventType L}.

Definition cons : pred {fset E} :=
  fun X => ~~ (PrimeG.gcf X).

Lemma cons_self (e : E) : cons [fset e].
Proof. rewrite /cons /=. exact: gcf_self. Qed.

Lemma cons_contr (X Y : {fset E}) : X `<=` Y -> cons Y -> cons X.
Proof. rewrite /cons=> ?. apply /contraNN. exact: gcf_ext. Qed.

Lemma cons_prop (X : {fset E}) (e e' : E) :
  e <= e' -> cons (e' |` X) -> cons (e |` X).
Proof. rewrite /cons=> ?. apply /contraNN. exact: gcf_hered. Qed.

Definition gcf_consMixin := 
  @PrimeC.EventStruct.Mixin E L _ cons cons_self cons_contr cons_prop.

Definition struct := PrimeC.EventType E L gcf_consMixin.

Lemma cfgE (p : pred E): 
  @PrimeC.cfg L struct p <-> 
  ca_closed p /\ cf_free p.
Proof. by []. Qed.

End ToPrimeC.

Module Export Exports.
Coercion struct : PrimeG.eventType >-> PrimeC.eventType.
Canonical struct.
End Exports.

End ToPrimeC.

End PrimeG.

Export PrimeG.EventStruct.Exports.
Export PrimeG.ToPrimeC.Exports.
Export PrimeG.OfPrimeC.Exports.
Export PrimeG.Theory.

Module Prime.

Module Export EventStruct.
Section ClassDef. 

Record mixin_of (E0 : Type) (L : Type) (b : Elem.EventStruct.class_of E0 L)
                (E := Elem.EventStruct.Pack b) := Mixin {
  cf : rel E; 

  _  : irreflexive cf;
  _  : symmetric cf;
  _  : hereditary (<=%O) cf; 
}.

Set Primitive Projections.
Record class_of (E : Type) (L : Type) := Class {
  base  : Elem.EventStruct.class_of E L;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Elem.EventStruct.class_of.

Structure type (L : Type) := Pack { sort; _ : class_of sort L }.

Local Coercion sort : type >-> Sortclass.

Variables (E : Type) (L : Type) (cT : type L).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') L in c.
Definition clone c of phant_id class c := @Pack E L c.
(* Definition clone_with disp' c of phant_id class c := @Pack disp' T c. *)

Definition pack :=
  fun bE b & phant_id (@Elem.EventStruct.class L bE) b =>
  fun m => Pack (@Class E L b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @Order.POrder.Pack tt cT class.
Definition lposetType := @lPoset.lPoset.Pack L cT class.
Definition elemEventType := @Elem.EventStruct.Pack L cT class.
End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Elem.EventStruct.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> Order.POrder.type.
Coercion lposetType : type >-> lPoset.eventType.
Coercion elemEventType : type >-> Elem.eventType.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical lposetType.
Canonical elemEventType.
End Exports.

End EventStruct.

Notation eventType := EventStruct.type.
Notation eventStruct := EventStruct.class_of.
Notation EventType E L m := (@EventStruct.pack E L _ _ id m).

Section Def.

Variable (L : Type) (E : eventType L).

Definition cf : rel E := EventStruct.cf (EventStruct.class E).

Definition cf_free (X : pred E) : Prop := 
  (* cf ⊓ (X × X) ≦ bot. *)
  forall x y, cf x y -> X x -> X y -> False.

(* configuration *)
Definition cfg (x : pred E) := 
  ca_closed x /\ cf_free x.

End Def.

Prenex Implicits cf cfg.

Module Export Syntax.
Notation "x \# y" := (cf x y) : prime_eventstruct_scope.
End Syntax.

Module Export Theory.
Section Theory.

Context {L : Type} {E : eventType L}.
Implicit Types (e x y z : E).

Lemma cf_irrefl : irreflexive (cf : rel E).
Proof. by case: E => ? [? []]. Qed.

Lemma cf_sym : symmetric (cf : rel E).
Proof. by case: E => ? [? []]. Qed.

Lemma cf_hered : hereditary (<=%O) (cf : rel E).
Proof. by case: E => ? [? []]. Qed.

Lemma cf_heredL x y z : 
  cf x y -> ca x z -> cf z y.
Proof. by rewrite cf_sym=> /cf_hered /[apply]; rewrite cf_sym. Qed.

Lemma cf_heredR x y z : 
  cf x y -> ca y z -> cf x z.
Proof. by apply cf_hered. Qed.

Lemma cf_heredLR x y z1 z2 : 
  cf x y -> ca x z1 -> ca y z2 -> cf z1 z2.
Proof. by do 2 (rewrite cf_sym; move=> /cf_hered /[apply]). Qed.

End Theory.
End Theory.

Module ToPrimeG.
Section ToPrimeG.

Context {L : Type} {E : eventType L}.

Definition gcf : pred {fset E} :=
  fun X => [exists e1 : X, exists e2 : X, (val e1) \# (val e2)].

Lemma gcf_self (e : E) : ~~ (gcf [fset e]).
Proof.
  rewrite /gcf /=. apply /fset_exists2P=> [] [] x [] y [].
  by move=> /fset1P -> /fset1P ->; rewrite cf_irrefl.
Qed.

Lemma gcf_ext (X Y : {fset E}) : X `<=` Y -> gcf X -> gcf Y.
Proof.
  rewrite /gcf=> H /= /fset_exists2P [] x [] y [].  
  move=> /(fsubsetP H) ? /(fsubsetP H) ??.
  by apply /fset_exists2P; exists x, y.
Qed.

Lemma gcf_hered (X : {fset E}) (e e' : E) :
  e <= e' -> gcf (e |` X) -> gcf (e' |` X).
Proof.
  rewrite /gcf=> Hca /fset_exists2P [] e1 [] e2 []. 
  rewrite !inE=> /orP [/eqP->|/[swap]]/orP[/eqP->|].
  - by rewrite cf_irrefl.
  - move=> I /cf_heredL/(_ Hca)?; apply /fset_exists2P.
    exists e', e2; split; by rewrite // ?inE (I, eqxx).
  - move=> I /cf_heredR/(_ Hca)?; apply /fset_exists2P.
    exists e1, e'; split; by rewrite // ?inE (I, eqxx).
  - move=> I1 I2 *; apply /fset_exists2P; 
    exists e1, e2; split; by rewrite // inE (I1, I2).
Qed.

Definition prime_gcfMixin := 
  @PrimeG.EventStruct.Mixin E L _ gcf gcf_self gcf_ext gcf_hered.

Definition struct := PrimeG.EventType E L prime_gcfMixin.

Lemma cfgE (p : pred E): 
  @PrimeC.cfg L struct p <-> cfg p.
Proof.
  rewrite PrimeG.ToPrimeC.cfgE /PrimeG.cf_free /PrimeG.gcf /=.
  split; move=> [? CF]; split=> //.
  - move=> x y xCy ??; have: gcf [fset x; y].
    - apply/fset_exists2P; exists x, y; rewrite ?inE ?eqxx xCy //.
    by apply/negP/CF=> ?; rewrite ?inE=> /orP[]/eqP->.
  move=> s S; apply/fset_exists2P=> [[x [y [*]]]].
  by apply/(CF x y)=> //; apply S.
Qed.

End ToPrimeG.

Module Export Exports.
Coercion struct : Prime.eventType >-> PrimeG.eventType.
Canonical struct.
End Exports.

End ToPrimeG.

End Prime.

Export Prime.EventStruct.Exports.
Export Prime.Syntax.
Export Prime.Theory.
Export Prime.ToPrimeG.Exports.

Section Prefix_Configuration.

Context {L : Type} {E : Prime.eventType L} {EG : PrimeG.eventType L}.

Lemma prime_prefix_cfg (e : E): 
  Prime.cfg (<= e).
Proof.
  exact/Prime.ToPrimeG.cfgE/prefix_cfg.
Qed.

Lemma primeG_prefix_cfg (e : EG): 
  PrimeG.cfg (<= e).
Proof.
  exact/PrimeG.ToPrimeC.cfgE/prefix_cfg.
Qed.

End Prefix_Configuration.


(* Section Test. *)

(* Context {L : Type} {E : Prime.eventType L}. *)
(* Variable (e1 e2 : E) (s : {fset E}). *)

(* Check (e1 <= e2 : bool). *)
(* Check (e1 \# e2 : bool). *)
(* Check (PrimeG.gcf s : bool). *)

(* End Test. *)
