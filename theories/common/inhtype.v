From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order.
From mathcomp Require Import eqtype choice fingraph path. 
From eventstruct Require Import utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* TODO: add scope? *)
Notation "?| T |" := (inhabited T)
  (at level 0, T at level 99, format "?| T |").

(* TODO: add scope? *)
Notation "??| A |" := (~~ pred0b A)
  (at level 0, A at level 99, format "??| A |").

Section Theory.
Implicit Types (aT rT : Type) (fT : finType).

Lemma nihn_inh_fun aT rT : 
  ~ ?|aT| -> ?|aT -> rT|.
Proof. 
  move=> H; constructor. 
  have fT: (forall x : aT, False).
  - move=> x; apply/H; constructor; exact/x. 
  by refine (fun x => match fT x with end).
Qed.

Lemma inh_impl aT rT : 
  (aT -> rT) -> ?|aT| -> ?|rT|.
Proof. move=> f [x]; exists; exact/(f x). Qed.

Lemma inh_iff aT rT : 
  (aT -> rT) -> (rT -> aT) -> ?|aT| <-> ?|rT|.
Proof. by move=> f g; split; apply/inh_impl. Qed.

Lemma fin_inhP fT : 
  reflect ?|fT| ??|fT|.
Proof. 
  apply/(equivP pred0Pn). 
  split; move=> [] //. 
  by move=> x; exists x.
Qed.

Lemma sub_fin_inhP fT (P : pred fT) (S : subType P) : 
  reflect ?|S| ??|P|.
Proof. 
  apply/(equivP pred0Pn). 
  split=> [[x Px] | [x]] //. 
  - exists; exact/(Sub x Px). 
  exists (val x); exact/(valP x).
Qed.


Variables (T : Type) (R : T -> T -> Type) (r : rel T).
Hypothesis (InhP  : forall x y, reflect ?|R x y| (r x y)).
Hypothesis (Refl  : forall x, R x x).
Hypothesis (Sym   : forall x y, R x y -> R y x).
Hypothesis (Trans : forall x y z, R x y -> R y z -> R x z).

Lemma is_inh_refl : reflexive r. 
Proof. move=> ?; apply/InhP; exists; exact/Refl. Qed.

Lemma is_inh_sym : symmetric r. 
Proof. move=> ??; apply/idP/idP=> /InhP[A]; apply/InhP; exists; exact/Sym. Qed.
  
Lemma is_inh_trans : transitive r. 
Proof. move=> ??? /InhP[A] /InhP[B]; apply/InhP; exists; exact/(Trans A B). Qed.

End Theory.


Module Inhabited.
Section ClassDef.

Record mixin_of T0 (b : Choice.class_of T0) 
                   (T := Choice.Pack b) := Mixin { 
  inh : T 
}.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base   : Choice.class_of T;
  mixin  : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Choice.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.

Definition pack :=
  fun bT b & phant_id (Choice.class bT) b =>
  fun m => Pack disp (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Canonical eqType.
Canonical choiceType.
Notation inhType := type.
Notation InhType T d m := (@pack T d _ _ id m).
Notation "[ 'inhType' 'of' T 'for' cT ]" := (@clone T _ cT _ id)
  (at level 0, format "[ 'inhType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'inhType' 'of' T ]" := [inhType of T for _]
  (at level 0, format "[ 'inhType'  'of'  T ]") : form_scope.
End Exports.

Module Export Def.
Section Def.
Context {disp : unit} {T : inhType disp}.

Definition inh : T := (inh (mixin (class T))).

End Def.

Section Homo.
Context {dispT dispU : unit} {T : inhType dispT} {U : inhType dispU}.
Implicit Types (f : T -> U).

Definition homo_inh f : bool := 
  (f inh == inh).

End Homo.
End Def.

Module Export Syntax.
Notation "{ 'homo' 'inh' f }" := (homo_inh f)
  (at level 0, f at level 99, format "{ 'homo'  'inh'  f }") : type_scope.
End Syntax.

End Inhabited.

Export Inhabited.Exports.
Export Inhabited.Def.
Export Inhabited.Syntax.


Module Bottom. 

Lemma disp : unit.
Proof. exact: tt. Qed.

Module Export Exports.
Notation botType := (@Inhabited.type disp).
Notation BotType T m := (@Inhabited.pack T disp _ _ id m).
End Exports.

Module Export Def.
Section Def.
Context {T : botType}.
Definition bot : T := @inh _ T. 
End Def.
End Def.

Module Export Syntax.
(* TODO: enforce that f is a function from/to botType ? *)
Notation "{ 'homo' 'bot' f }" := (homo_inh f)
  (at level 0, f at level 99, format "{ 'homo'  'bot'  f }") : type_scope.
End Syntax.

End Bottom. 

Export Bottom.Exports.
Export Bottom.Def.
Export Bottom.Syntax.


Definition nat_inhMixin := @Inhabited.Mixin nat _ 0.
Canonical nat_inhType := Eval hnf in InhType nat tt nat_inhMixin.
