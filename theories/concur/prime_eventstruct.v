From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From mathcomp Require Import eqtype choice order finmap fintype. 
From RelationAlgebra Require Import lattice boolean.
From eventstruct Require Import utils relalg pomset.

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

Record mixin_of (E0 : Type) (L : Type) (eb : LPoset.LPoset.class_of E0 L)
                (E := LPoset.LPoset.Pack eb) := Mixin {
  _ : fin_cause (ca : rel E)
}.

Set Primitive Projections.
Record class_of (E : Type) (L : Type) := Class {
  base  : LPoset.LPoset.class_of E L;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> LPoset.LPoset.class_of.

Structure type (L : Type) := Pack { sort; _ : class_of sort L }.

Local Coercion sort : type >-> Sortclass.

Variables (E : Type) (L : Type) (cT : type L).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') L in c.
Definition clone c of phant_id class c := @Pack E c.
(* Definition clone_with disp' c of phant_id class c := @Pack disp' T c. *)

Definition pack :=
  fun bE b & phant_id (@LPoset.LPoset.class L bE) b =>
  fun m => Pack (@Class E L b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @Order.POrder.Pack tt cT class.
Definition lposetType := @LPoset.LPoset.Pack L cT class.
End ClassDef.

Module Export Exports.
Coercion base : class_of >-> LPoset.LPoset.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> Order.POrder.type.
Coercion lposetType : type >-> LPoset.eventType.
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


Module Prime.

Module Export EventStruct.
Section ClassDef. 

Record mixin_of (E0 : Type) (L : Type) (b : Elem.EventStruct.class_of E0 L)
                (E := Elem.EventStruct.Pack b) := Mixin {
  cf : rel E; 

  _  : irreflexive cf;
  _  : symmetric cf;
  _  : hereditary ca cf; 
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
Definition lposetType := @LPoset.LPoset.Pack L cT class.
Definition elemEventType := @Elem.EventStruct.Pack L cT class.
End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Elem.EventStruct.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> Order.POrder.type.
Coercion lposetType : type >-> LPoset.eventType.
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

Lemma prefix_cf_free e : cf_free (<= e).
Proof. 
  move=> e1 e2 /=; rewrite /le_bool.
  move=> /(@cf_heredLR e1 e2 e e) /[apply] /[apply]. 
  by rewrite cf_irrefl.
Qed.

Lemma prefix_cfg e : cfg (<= e).
Proof. split; [exact/prefix_ca_closed | exact/prefix_cf_free]. Qed.

End Theory.
End Theory.

End Prime.

Export Prime.EventStruct.Exports.
Export Prime.Syntax.
Export Prime.Theory.


Module PrimeG.

Module EventStruct.
Section ClassDef.

Record mixin_of (E0 : Type) (L : Type) (b : Elem.EventStruct.class_of E0 L)
                (E := LPoset.LPoset.Pack b) := Mixin {
  gcf : pred {fset E};

  _ : forall (e : E), ~~ (gcf [fset e]);
  _ : forall (X Y : {fset E}), X `<=` Y -> gcf X -> gcf Y;
  _ : forall X e e', e <= e' -> gcf (X `|` [fset e]) -> gcf (X `|` [fset e'])
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
Definition lposetType := @LPoset.LPoset.Pack L cT class.
Definition elemEventType := @Elem.EventStruct.Pack L cT class.
End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Elem.EventStruct.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> Order.POrder.type.
Coercion lposetType : type >-> LPoset.eventType.
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

Definition gcf_free (x : {fset E}) := ~~ (gcf x).

Definition cfg (p : pred E) := 
  forall (s : {fset E}), {subset s <= p} -> gcf_free s.

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
  forall X (e e' : E), e <= e' -> gcf (X `|` [fset e]) -> gcf (X `|` [fset e']).
Proof. by case: E => ? [? []]. Qed.

End Theory.
End Theory.

Module OfPrime.
Section OfPrime.

Context {L : Type} {E : Prime.eventType L}.

Definition gcf : pred {fset E} :=
  fun X => [exists e1 : X, exists e2 : X, (val e1) \# (val e2)].

Lemma gcf_self (e : E) : ~~ (gcf [fset e]).
Proof.
  rewrite /gcf /=; apply /fset_exists2P=> [] [] x [] y [].
  by move=> /fset1P -> /fset1P ->; rewrite cf_irrefl.
Qed.

Lemma gcf_ext (X Y : {fset E}) : X `<=` Y -> gcf X -> gcf Y.
Proof.
  rewrite /gcf=> H /= /fset_exists2P [] x [] y [].  
  move=> /(fsubsetP H) ? /(fsubsetP H) ??.
  by apply /fset_exists2P; exists x, y.
Qed.

Lemma gcf_hered (X : {fset E}) (e e' : E) :
  e <= e' -> gcf (X `|` [fset e]) -> gcf (X `|` [fset e']).
Proof.
  rewrite /gcf=> Hca /fset_exists2P [] e1 [] e2 []. 
  rewrite !in_fsetU=> /orP [] + /orP []; last first. 
  - by move=> /fset1P -> /fset1P ->; rewrite cf_irrefl.
  - move=> /fset1P -> ? H; apply /fset_exists2P; exists e', e2.
    rewrite !in_fsetU; split; try (apply /orP); try by left.
    + by right; apply /fset1P.
    by apply: (cf_heredL H).
  - move=> ? /fset1P -> H; apply /fset_exists2P; exists e1, e'.
    rewrite !in_fsetU; split; try (apply /orP); try by left.
    + by right; apply /fset1P.
    by apply: (cf_heredR H). 
  move=> ???; apply /fset_exists2P; exists e1, e2. 
  by rewrite !in_fsetU; split; try (apply /orP); try by left.
Qed.

Definition prime_gcfMixin := 
  @EventStruct.Mixin E L _ gcf gcf_self gcf_ext gcf_hered.

Definition prime_primeG := EventType E L prime_gcfMixin.

End OfPrime.

Module Export Exports.
Coercion prime_primeG : Prime.eventType >-> eventType.
Canonical prime_primeG.
End Exports.

End OfPrime.

End PrimeG.

Export PrimeG.EventStruct.Exports.
Export PrimeG.OfPrime.Exports.
Export PrimeG.Theory.

(* Section Test. *)

(* Context {L : Type} {E : Prime.eventType L}. *)
(* Variable (e1 e2 : E) (s : {fset E}). *)

(* Check (e1 <= e2 : bool). *)
(* Check (e1 \# e2 : bool). *)
(* Check (PrimeG.gcf s : bool). *)

(* End Test. *)

Module PrimeC.

Module EventStruct.
Section ClassDef.

Record mixin_of (T0 : Type) (b : Pomset.Pomset.class_of T0)
                (T := Pomset.Pomset.Pack tt b) := Mixin {
  cons : pred {fset T};

  _ : forall (e : T), cons [fset e];
  _ : forall (X Y : {fset T}), X `<=` Y -> cons Y -> cons X;
  _ : forall X e e', e <= e' -> cons (X `|` [fset e']) -> cons (X `|` [fset e])
}.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base  : Pomset.Pomset.class_of T;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Pomset.Pomset.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.

Definition pack :=
  fun bT b & phant_id (@Pomset.Pomset.class disp bT) b =>
  fun m => Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition porderType := @Order.POrder.Pack disp cT class.
Definition pomsetEventType := @Pomset.Pomset.Pack disp cT class.
End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Pomset.Pomset.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> Order.POrder.type.
Coercion pomsetEventType : type >-> Pomset.eventType.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical pomsetEventType.
End Exports.

End EventStruct.

Export EventStruct.Exports.

Notation eventType := EventStruct.type.
Notation eventStruct := EventStruct.class_of.
Notation EventType disp T m := (@EventStruct.pack T disp _ _ id m).

Section Def.

Variable (disp : unit) (E : eventType disp).

Definition cons : pred {fset E} :=
  EventStruct.cons (EventStruct.class E).

End Def.

Prenex Implicits cons.

Module Import Theory.
Section Theory.

Context {disp : unit} {E : eventType disp}.

Lemma cons_self : forall (e : E), cons [fset e].
Proof. by case: E => ? [? []]. Qed.

Lemma cons_contr : forall (X Y : {fset E}), X `<=` Y -> cons Y -> cons X.
Proof. by case: E => ? [? []]. Qed.

Lemma cons_prop :
  forall X (e e' : E), e <= e' -> cons (X `|` [fset e']) -> cons (X `|` [fset e]).
Proof. by case: E => ? [? []]. Qed.

End Theory.
End Theory.

Module OfPrimeG.
Section OfPrimeG.

Context {disp : unit} {E : PrimeG.eventType disp}.

Definition cons : pred {fset E} :=
  fun X => ~~ (PrimeG.gcf X).

Lemma cons_self (e : E) : cons [fset e].
Proof. rewrite /cons /=. exact: gcf_self. Qed.

Lemma cons_contr (X Y : {fset E}) : X `<=` Y -> cons Y -> cons X.
Proof. rewrite /cons=> ?. apply /contraNN. exact: gcf_ext. Qed.

Lemma cons_prop (X : {fset E}) (e e' : E) :
  e <= e' -> cons (X `|` [fset e']) -> cons (X `|` [fset e]).
Proof. rewrite /cons=> ?. apply /contraNN. exact: gcf_hered. Qed.

Definition gcf_consMixin := 
  @EventStruct.Mixin E _ cons cons_self cons_contr cons_prop.

Definition primeG_primeC := EventType disp E gcf_consMixin.

End OfPrimeG.

Module Export Exports.
Coercion primeG_primeC : PrimeG.eventType >-> eventType.
Canonical primeG_primeC.
End Exports.

End OfPrimeG.

Module ToPrimeG.
Section ToPrimeG.

Context {disp : unit} {E : PrimeC.eventType disp}.

Definition gcf : pred {fset E} :=
  fun X => ~~ (cons X).

Lemma gcf_self (e : E) : ~~ (gcf [fset e]).
Proof. by rewrite /gcf cons_self. Qed.

Lemma gcf_ext (X Y : {fset E}) : X `<=` Y -> gcf X -> gcf Y.
Proof. rewrite /gcf=> H. apply: contraNN. exact: cons_contr. Qed.

Lemma gcf_hered (X : {fset E}) (e e' : E) :
  e <= e' -> gcf (X `|` [fset e]) -> gcf (X `|` [fset e']).
Proof. rewrite /gcf=> H. apply: contraNN. exact: cons_prop. Qed.

Definition cons_gcfMixin := 
  @PrimeG.EventStruct.Mixin E _ gcf gcf_self gcf_ext gcf_hered.

Definition primeC_primeG := PrimeG.EventType disp E cons_gcfMixin.

End ToPrimeG.

Module Export Exports.
Coercion primeC_primeG : PrimeC.eventType >-> PrimeG.eventType.
Canonical primeC_primeG.
End Exports.

End ToPrimeG.

End PrimeC.
