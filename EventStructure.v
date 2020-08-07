From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order eqtype. 
(*Import Order.LTheory.
Open Scope order_scope.
Notation evType := (porderType tt).*)
Declare Scope hb_scope.
Delimit Scope hb_scope with G.
Open Scope hb_scope.

(*******************************************************************************
HB.mixin Record eqType_of_Type T := {
  op  : rel T;
  eqP : Equality.axiom op;
}.

HB.structure Definition eq := { T of eqType_of_Type T }.


Canonical hb_eqMixin {T : eq.type} := @EqMixin T _ eqP.
Canonical hb_eqType {T : eq.type} := Eval hnf in EqType T hb_eqMixin.
Definition foo {T : eq.type} (e : T) := e == e.

HB.mixin Record porederType_of_eqType T of eq T := {
  le        : rel T;
  le_refl   : reflexive     le;
  le_anti   : antisymmetric le;
  le_trans  : transitive    le
}.

HB.structure Definition porder := { T of eq T & porederType_of_eqType T }.
(*Definition bar : eqType_of_Type porder.type := eq.Build porder.type op eqP.

HB.instance porder.type .*)
Fail Definition foo1 {T : porder.type} (e : T) := e == e.
Fail Canonical porder_eqMixin {T : porder.type} := @EqMixin T _ eqP.

(* we need this for such 'finite' definition *)
Definition finite {T : eq.type} (a : pred T) :=  exists (s : seq T), forall x, x \in a -> x \in s.
(* in *)
HB.mixin Record event_struct_of_porder_confl E of porder E & confl E := 
{
    finite_downward_closure : forall e : E, finite (downward_closure e); (***)
    consist_confl   : forall e1 e2 e3 : E,
      (e2 # e1) = true -> (le e1 e3) = true -> (e2 # e3) = true; (***)
}.
*******************************************************************************)
(*Notation sw := 
  (ltac:(let f := fresh "_top_" in let s := fresh "_s_" in move=> f s; move: f s)).*)

(*HB.mixin Record choiseType_of_Type T := {
  find : pred T -> nat -> option T;
  ax1 : forall P n x, find P n = Some x -> (P x) = true;
  ax2 : forall P : pred T, (exists x, (P x = true)) -> exists n, (find P n);
  ax3 : forall P Q : pred T, P =1 Q -> find P =1 find Q
}.*)

Definition finite {T : Type} (a : pred T) := 
    exists (n : nat) (f : 'I_n -> T), forall x, x \in a -> exists k, f k = x.

HB.mixin Record eqType_of_Type T := {
  op  : rel T;
  eqP : Equality.axiom op;
}.

HB.structure Definition eq := { T of eqType_of_Type T }.

HB.mixin Record porederType_of_eqType T of eq T := {
  le        : rel T;
  le_refl   : reflexive     le;
  le_anti   : antisymmetric le;
  le_trans  : transitive    le
}.

HB.structure Definition porder :=
  { T of eq T & porederType_of_eqType T }.
Notation "e1 <= e2" := (le e1 e2).

HB.mixin Record confl_of_Type T := {
  conflict : rel T;
  confl_irrefl    : irreflexive conflict;
  confl_symm      : symmetric conflict;
}.

HB.structure Definition confl :=
  { T of confl_of_Type T }.
Notation "a # b" := (conflict a b) (at level 0) : hb_scope.

Definition downward_closure {T : porder.type} (e : T) := le^~ e.
Notation "⎡ e ⎤" := (downward_closure e).
(*Definition finite_causes_axiom {E : porder.type} := forall e : E, finite (downward_closure e).*)
Definition finite_causes_axiom {E : porder.type} (e : E) := finite (downward_closure e).

HB.mixin Record event_struct_of_porder_confl (E : Type) of porder E & confl E := {
    finite_axiom : forall (e : E), finite_causes_axiom e;
    consist_confl   : forall e1 e2 e3 : E,
      (e2 # e1) = true -> (le e1 e3) = true -> (e2 # e3) = true; (*???*)
}.
HB.structure Definition evstruct := { E of porder E & confl E & event_struct_of_porder_confl E }.

Canonical evstruct_eqMixin {T : evstruct.type} := @EqMixin T op eqP.
Canonical hb_eqType {T : evstruct.type} := Eval hnf in EqType T evstruct_eqMixin.

(*Section orderMixinDef.
Context {E : evstruct.type}.
Implicit Type e : E.
Definition lt e1 e2 := (e2 != e1) && (le e1 e2).
Lemma lt_def x y : lt x y = (y != x) && (le x y).
Proof. by []. Qed.

Definition orderMixin :=
  LePOrderMixin lt_def le_refl le_anti le_trans.

Lemma evstruct_display : unit. Proof. exact: tt. Qed.

End orderMixinDef.
Canonical porderType := POrderType evstruct_display evstruct.type orderMixin.*)

Section Specifications.
Context {E : evstruct.type}.
Implicit Types (p : pred E) (e : E).

Definition downward_closed p := forall e1 e2, e1 \in p -> e2 <= e1 -> e2 \in p.

Lemma downward_closureE e1 e2: (e2 \in ⎡e1⎤) = (e2 <= e1).
Proof. by []. Qed.

Lemma downward_closed_downward_closure e : downward_closed ⎡e⎤.
Proof. move=> ??? /le_trans. by apply. Qed.

Definition conflict_free p := forall e1 e2, e1 \in p -> e2 \in p -> ~~ (e1 # e2).
Definition configuration p := (conflict_free p * downward_closed p)%type.

Lemma config_downward_closure e: configuration (downward_closure e).
Proof.
split=> [e1 e2 *|]; last by apply: downward_closed_downward_closure.
case confl: (e1 # e2)=> //=. rewrite -(confl_irrefl e).
by rewrite (consist_confl e2)// confl_symm (consist_confl e1)// confl_symm.
Qed.

End Specifications.

Section Option_evstruct.
Context {E : evstruct.type}.
Implicit Types e : option E.

Definition op e1 e2 := 
  match e1, e2 with
  | some e1, some e2 => e1 == e2
  | None, None       => true
  | _,    _          => false
  end.

Lemma eqP: Equality.axiom op.
Proof. 
case=> [e1|][e2|]//=; first case EQ: (e1 == e2); constructor=> //;
move: EQ=> /eqP; first by move=>->. by move=> EQ [/EQ].
Qed.

Definition le e1 e2 := 
  match e1, e2 with
  | some e1, some e2 => e1 <= e2
  | None, None       => true
  | _,    _          => false
  end.

Lemma le_refl: reflexive le.
Proof. case=> //. by apply: le_refl. Qed.

Lemma le_symm: antisymmetric le.
Proof. by case=> [?|][]// ? /le_anti->. Qed.

Lemma le_trans: transitive le.
Proof. case=> [?|][?|][?|]//. by exact: le_trans. Qed.

Definition conflict e1 e2 := 
  match e1, e2 with
  | some e1, some e2 => e1 # e2
  | None, None       => false
  | _,    _          => false
  end.

Lemma confl_irrefl: irreflexive conflict.
Proof. case=> //; by exact: confl_irrefl. Qed.

Lemma confl_symm: symmetric conflict.
Proof. case=> [?|][]//; by exact: confl_symm. Qed.



(*8 Definition Z_Monoid_axioms : Monoid_of_Type Z :=
9 Monoid_of_Type.Build Z 0%Z Z.add Z.add_assoc Z.add_0_l Z.add_0_r.
10
11 HB.instance Z Z_Monoid_axioms.*)

(*Definition option_porder_axioms := porder_of_.


HB.instance *)


End Option_evstruct.

(*Definition option_eqtype_axiom {E : evstruct.type} :
  eqType_of_Type (option E) :=
  eqType_of_Type.Build (option E) oop oeqP.
HB.instance*)


Section Parallel_Product.
Context {E0 E1 : evstruct.type}.
Implicit Types e : (option E0 * option E1)%type.

Definition le e e' := 
  match e, e' with
  | (some e1, some e2), (some e'1, some e'2) => (e1 <= e'1) && (e2 <= e'2)
  | _, _                                     => false
  end.

Lemma : reflexive le;.
Proof.
  
Qed.


End Parallel_Product.

