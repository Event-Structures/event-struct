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

Definition hereditary {T : Type} (ca cf : rel T) := 
  forall x y z : T, cf x y -> ca y z -> cf x z.

Module Prime.

Module EventStruct.
Section ClassDef. 

Record mixin_of (T0 : Type) (b : Pomset.Pomset.class_of T0)
                (T := Pomset.Pomset.Pack tt b) := Mixin {
  cf : rel T; 

  _  : irreflexive cf;
  _  : symmetric cf;
  _  : hereditary (<=%O) cf; 
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
Coercion base : EventStruct.class_of >-> Pomset.Pomset.class_of.
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

Definition cf : rel E := EventStruct.cf (EventStruct.class E).

Definition cf_free (X : pred E) : Prop := 
  cf ⊓ (X × X) ≦ bot.

(* configuration *)
Definition cfg (x : pred E) := 
  ca_closed x /\ cf_free x.

End Def.

Prenex Implicits cf.

Module Import Syntax.
Notation "x \# y" := (cf x y) : prime_eventstruct_scope.
End Syntax.

Module Export Theory.
Section Theory.

Context {disp : unit} {E : eventType disp}.

Lemma cf_irrefl : irreflexive (cf : rel E).
Proof. by case: E => ? [? []]. Qed.

Lemma cf_sym : symmetric (cf : rel E).
Proof. by case: E => ? [? []]. Qed.

Lemma cf_hered : hereditary (<=%O) (cf : rel E).
Proof. by case: E => ? [? []]. Qed.

Lemma prefix_cf_free (e : E) : cf_free (<= e).
Proof. 
  move=> e1 e2 /=; rewrite /le_bool.
  case/andP=> /cf_hered cf /andP[+ {}/cf].
  rewrite cf_sym; move/cf_hered/[apply].
  by rewrite cf_irrefl.
Qed.

Lemma prefix_cfg (e : E) : cfg (<= e).
Proof.
  split; first by apply: prefix_ca_closed.
  exact: prefix_cf_free.
Qed.

End Theory.
End Theory.

End Prime.

Export Prime.EventStruct.Exports.
Export Prime.Syntax.
Export Prime.Theory.

Module PrimeG.

Module EventStruct.
Section ClassDef.

Record mixin_of (T0 : Type) (b : Pomset.Pomset.class_of T0)
                (T := Pomset.Pomset.Pack tt b) := Mixin {
  Conf : pred {fset T};

  _ : forall (e : T), ~~ (Conf [fset e]);
  _ : forall (X Y : {fset T}), X `<=` Y -> Conf X -> Conf Y;
  _ : forall X e e', e <= e' -> Conf (X `|` [fset e]) -> Conf (X `|` [fset e'])
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

Definition gcf : pred {fset E} :=
  EventStruct.Conf (EventStruct.class E).

Definition gcf_free (x : {fset E}) := ~~ (gcf x).

End Def.

Prenex Implicits gcf.

Module Import Theory.
Section Theory.

Context {disp : unit} {E : eventType disp}.

Lemma gcf_self : forall (e : E), ~~ (gcf [fset e]).
Proof. by case: E => ? [? []]. Qed.

Lemma gcf_ext : forall (X Y : {fset E}), X `<=` Y -> gcf X -> gcf Y.
Proof. by case: E => ? [? []]. Qed.

Lemma gcf_hered :
  forall X (e e' : E), e <= e' -> gcf (X `|` [fset e]) -> gcf (X `|` [fset e']).
Proof. by case: E => ? [? []]. Qed.

End Theory.
End Theory.

Module GenOfPrime.
Section GenOfPrime.

Context {disp : unit} {E : Prime.eventType disp}.

Definition gcf_of_cf : pred {fset E} :=
  fun X => [exists e1 : X, exists e2 : X, (val e1) \# (val e2)].

Lemma cf_self (e : E) : ~~ (gcf_of_cf [fset e]).
Proof.
  rewrite /gcf_of_cf /=. apply /existsP => [] [] /= e1 /existsP [] /= e2.
  move: e1 e2 => [] e1 p1 /= [] e2 p2 /=.
  have: e1 = e.
  - exact: fset1P.
  move=> ->.
  have: e2 = e.
  - exact: fset1P.
  by move=> ->; rewrite cf_irrefl.
Qed.

Lemma cf_ext (X Y : {fset E}) : X `<=` Y -> gcf_of_cf X -> gcf_of_cf Y.
Proof.
  move=> XsubY.
  rewrite /gcf_of_cf => /existsP [] /= [] e1 p1 /existsP [] /= [] e2 p2 /= cf12.
  apply /existsP => /=.
  have: e1 \in Y.
  { by move: XsubY p1 => /fsubsetP /[apply]. }
  move=> py1. exists (FSetSub py1).
  apply /existsP => /=.
  have: e2 \in Y.
  { by move: XsubY p2 => /fsubsetP /[apply]. }
  move=> py2. exists (FSetSub py2).
  move=> /=. exact: cf12.
Qed.

Lemma cf_hered (X : {fset E}) (e e' : E) :
  e <= e' -> gcf_of_cf (X `|` [fset e]) -> gcf_of_cf (X `|` [fset e']).
Proof.
  move=> ca12. rewrite /gcf_of_cf => /existsP [] /= [] /= e1.
  rewrite in_fsetU => /orP [H|H] /existsP [] /= [] /= e2.
  all: rewrite in_fsetU => /orP [H'|H'] cf12.
  { apply /existsP. exists (FSetSub (fsetU1l e' H)).
    apply /existsP. exists (FSetSub (fsetU1l e' H')).
    exact: cf12. }
  { apply /existsP. exists (FSetSub (fsetU1l e' H)).
    apply /existsP. exists (FSetSub (fsetU1r X e')).
    apply: cf_hered; first exact: cf12.
    have: e2 = e by apply: fset1P.
    by move=> ->. }
  { apply /existsP. exists (FSetSub (fsetU1r X e')).
    apply /existsP. exists (FSetSub (fsetU1l e' H')).
    rewrite cf_sym. apply: cf_hered; last exact: ca12.
    have: e1 = e by apply: fset1P.
    move=> <-. by rewrite cf_sym. }
  move: cf12.
  have: e1 = e by apply: fset1P.
  have: e2 = e by apply: fset1P.
  move=> -> ->. by rewrite cf_irrefl.
Qed.

Definition gcf_primeMixin :=
  @EventStruct.Mixin E _ gcf_of_cf cf_self cf_ext cf_hered.

Canonical conf_primePrime := EventType disp E gcf_primeMixin.

End GenOfPrime.
End GenOfPrime.

End PrimeG.

Export PrimeG.EventStruct.Exports.
Export PrimeG.Theory.
Export PrimeG.GenOfPrime.
