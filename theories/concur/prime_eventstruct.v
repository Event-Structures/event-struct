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

Definition id_hack {E} := @id E.

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

Module Import Theory.
Section Theory.

Context {L : Type} {E : eventType L}.

Lemma cons_self : forall (e : E), cons [fset e].
Proof. by case: E => ? [? []]. Qed.

Lemma cons_contr : forall (X Y : {fset E}), X `<=` Y -> cons Y -> cons X.
Proof. by case: E => ? [? []]. Qed.

Lemma cons_prop :
  forall X (e e' : E), e <= e' -> cons (e' |` X) -> cons (e |` X).
Proof. by case: E => ? [? []]. Qed.

Lemma cons_ca_contr (X Y : {fset E}) (df : E):
  (forall x, x \in X -> exists2 y, y \in Y & x <= y) ->
  cons Y -> cons X.
Proof.
  move=> C Cy; have [n leMn] := ubnP (#|` (X `\` Y)|).
  elim: n => // n IHn in X leMn C *.
  case: n IHn leMn=> [*|n IHn leMn].
  - by have /cons_contr/(_ Cy): X `<=` Y by rewrite -fsetD_eq0 -cardfs_eq0 -leqn0.
  case (fset_0Vmem (X `\` Y))=> [/eqP| [x]].
  - rewrite fsetD_eq0=> /cons_contr; exact.
  move=> /[dup] iXY.
  rewrite inE=> /andP[? /[dup] /C[y iy xLy] /fsetD1K<-].
  apply/(cons_prop xLy)/IHn=> [|z].
  - rewrite fsetDUl.
    have/eqP->: ([fset y] `\` Y == fset0) by rewrite fsetD_eq0 fsub1set.
    rewrite fset0U fsetDDl fsetUC -fsetDDl.
    rewrite (cardfsD1 x) iXY /= in leMn; move: #|`_| leMn=> sz. 
    by rewrite add1n=> /=.
  rewrite ?inE=> /orP[/eqP->|/andP[_ /C //]].
  by exists y.
Qed.

Lemma prefix_cf_free (e : E) : cf_free (<= e).
Proof. 
  move=> X S; apply/(@cons_ca_contr _ [fset e] e)/cons_self.
  move=> x i; exists e; rewrite ?inE //; exact/S.
Qed.

Lemma prefix_cfg (e : E) : cfg (<= e).
Proof.
  split; [exact/prefix_ca_closed | exact/prefix_cf_free].
Qed.

End Theory.
End Theory.

End PrimeC.

Export PrimeC.EventStruct.Exports.
Export PrimeC.Theory.
Export PrimeC.Syntax.

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
