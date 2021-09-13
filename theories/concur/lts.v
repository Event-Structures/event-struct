From RelationAlgebra Require Import lattice monoid rel.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq path. 
From eventstruct Require Import utils relalg.

(******************************************************************************)
(* This file provides a theory of labelled transition systems.                *)
(* TODO.                                                                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* TODO: move to more appropriate place *)
Notation lang L := (seq L -> Prop).

Declare Scope lts_scope.
Delimit Scope lts_scope with lts.

Local Open Scope lts_scope.

Reserved Notation "s1 '--[' l ']-->' s2" (at level 22, no associativity).
Reserved Notation "s1 '-->' s2" (at level 55, right associativity).
Reserved Notation "s1 '-->?' s2" (at level 55, right associativity).
Reserved Notation "s1 '-->+' s2" (at level 22, right associativity).
Reserved Notation "s1 '-->*' s2" (at level 22, right associativity).

Module Export LTS.

Section ExLab.
Context {S L : Type}.

(* TODO: remove copypaste from `rewriting_system.v` *)
Definition exlab {S L : Type} (tr : L -> hrel S S) : hrel S S := 
  fun s1 s2 => exists l, tr l s1 s2.

End ExLab.

Module LTS.
Section ClassDef. 

Record mixin_of (S0 : Type) (L : Type)
                (sb : Equality.class_of S0)
                (S := Equality.Pack sb) := Mixin {
  tr : L -> rel S;
}.

Set Primitive Projections.
Record class_of (S : Type) (L : Type) := Class {
  base  : Equality.class_of S;
  mixin : mixin_of L base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Equality.class_of.

Structure type (L : Type) := Pack { sort; _ : class_of sort L }.

Local Coercion sort : type >-> Sortclass.

Variables (S : Type) (L : Type) (cT : type L).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') L in c.
Definition clone c of phant_id class c := @Pack S c.

Definition pack :=
  fun bS b & phant_id (@Equality.class bS) b =>
  fun m => Pack (@Class S L b m).

Definition eqType := @Equality.Pack cT class.
End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Equality.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
End Exports.

End LTS.

Export LTS.Exports.

Notation ltsType := LTS.type.
Notation LTSType S L m := (@LTS.pack S L _ _ id m).

Section Def.
Context {L : Type} (S : ltsType L).

Definition tr : L -> rel S := LTS.tr (LTS.class S).

End Def.

Module Export Syntax.
Notation "s1 '--[' l ']-->' s2" := (tr l s1 s2) : lts_scope.
Notation "s1 '-->' s2"  := (exlab tr)   : lts_scope.
Notation "s1 '-->?' s2" := (exlab tr)^? : lts_scope.
Notation "s1 '-->+' s2" := (exlab tr)^+ : lts_scope. 
Notation "s1 '-->*' s2" := (exlab tr)^* : lts_scope.
End Syntax.

End LTS.

(* Context {L : Type} {S : ltsType L}. *)
(* Variable (l : L) (s1 s2 : S). *)
(* Check (s1 --[l]--> s2). *)

Module Export Step. 
Section Def.
Context {L : Type} (S : ltsType L).

Structure step : Type := mk_step { 
  lbl : L; src : S; dst : S;  
  _   : src --[lbl]--> dst;
}.

Definition linkable : rel step := 
  fun s t => dst s == src t. 

End Def.

Prenex Implicits lbl src dst.

Section EQ. 
Context {L : eqType} (S : ltsType L).

Definition prod_of_step : step S -> L * S * S := 
  fun s => (lbl s, src s, dst s).

Lemma prod_of_step_inj : injective prod_of_step.
Proof. 
  rewrite /prod_of_step; move=> x y /= []. 
  case x=> l1 s1 d1 H1; case y=> l2 s2 d2 H2 /=. 
  move=> Hl Hs Hd; move: H1 H2; rewrite Hl Hs Hd=> H1 H2.
  have ->: H1 = H2=> //.
  exact/bool_irrelevance.
Qed.

Definition step_eqMixin := InjEqMixin prod_of_step_inj.
Canonical step_eqType := Eval hnf in EqType (step S) step_eqMixin.

End EQ.
End Step.


Module Export FinTrace. 
Section Def. 
Context {L : Type} (S : ltsType L).

Structure ftrace : Type := FinTrace { 
  ftrace_val :> seq (step S); 
  _          :  sorted (@linkable L S) ftrace_val;
}.

Definition labels : ftrace -> seq L := map lbl. 

Definition states : ftrace -> seq S := 
  fun tr => 
    let hd := omap src (ohead tr) in
    let tl := map dst tr in
    ocons hd tl.

Definition ftraces_at : S -> pred ftrace := 
  fun s tr => s == head s (states tr).

(* TODO: this is actually a fmap on (A -> Prop) functor. *)
Definition lts_lang : S -> lang L := 
  fun s w => exists tr, w = labels tr /\ ftraces_at s tr.

End Def. 
End FinTrace.


Module Export Simulation.

Module Simulation.
Section ClassDef. 

(* TODO: simulation between lts labelled by different labels? *)
Context {L : Type} (S T : ltsType L).
Implicit Types (R : hrel S T).

Record mixin_of R := Mixin {
  _ : forall (l : L) (s1 : S) (t1 t2 : T), 
        R s1 t1 -> t1 --[l]--> t2 -> exists s2, 
        R s2 t2 /\ s1 --[l]--> s2;  
}.

Set Primitive Projections.
Record class_of R := Class {
  mixin : mixin_of R;
}.
Unset Primitive Projections.

Structure type := Pack { apply : S -> T -> Prop ; _ : class_of apply }.

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

End Simulation.

Export Simulation.Exports.

Notation sim := Simulation.type.

Module Syntax. 
Notation "S ~>~ T" := (sim S T) (at level 50) : lts_scope.
End Syntax. 

Section Theory.
Import Syntax. 
Context {L : Type} {S T : ltsType L}.
Implicit Types (R : S ~>~ T).

Lemma sim_step R l s1 t1 t2 :
  R s1 t1 -> (t1 --[l]--> t2) -> exists s2, R s2 t2 /\ (s1 --[l]--> s2).
Proof. case: R=> ? [[H]] /=; exact/H. Qed.

(* Lemma sim_stepE R l :  *)
(*   (R : hrel S T) ⋅ (tr l : hrel T T) ≦ (tr l : hrel S S) ⋅ (R : hrel S T). *)
(* Proof. admit. Admitted. *)

Lemma sim_traces R s t : 
  R s t -> lts_lang s ≦ lts_lang t.
Proof. admit. Admitted.

End Theory.

End Simulation. 


