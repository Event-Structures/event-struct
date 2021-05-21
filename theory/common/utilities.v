From Coq Require Import Lia Relations.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun eqtype.
From mathcomp Require Import seq path fingraph fintype.
From RelationAlgebra Require Import lattice monoid boolean rel fhrel kat_tac.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Unset Strict Implicit.

(* ************************************************************************** *)
(*     Some automation with hints and tactics                                 *)
(* ************************************************************************** *)

(***** ssrnatlia ******)

(*Transformation of a constraint (x # y) where (x y : nat) and # is a comparison
relation into the corresponding constraint (x #' y) where #' is
the std lib analogue of #. The transformation is performed on the first such formula
found either in the context or the conclusion of the goal *)
Ltac ssrnatify_rel :=
 match goal with
  (* less or equal (also codes for strict comparison in ssrnat) *)
  | H : is_true (leq _ _) |- _ => move/leP: H => H
  | H : context [ is_true (leq ?a ?b)] |- _ =>
     rewrite <- (rwP (@leP a b)) in H
  | |- is_true (leq _ _) => apply/leP
  | |- context [ is_true (leq ?a ?b)] => rewrite <- (rwP (@leP a b))
  (* Boolean equality *)
  | H : is_true (@eq_op _ _ _) |- _ => move/eqP: H => H
  | |- is_true (@eq_op _ _ _) => apply/eqP
  | H : context [ is_true (@eq_op _ _ _)] |- _ =>
     rewrite <-  (rwP (@eqP _ _ _)) in H
  | |- context [ is_true (@eq_op _ ?x ?y)] => rewrite <- (rwP (@eqP _ x y))
  (* Negated boolean equality *)
  | H : is_true (negb (@eq_op _  _ _)) |- _ => move/eqP: H => H
  | |- is_true (negb (@eq_op _  _ _)) => apply/eqP
  | H : context [ is_true (negb (@eq_op _ _ _))] |- _ =>
     rewrite <-  (rwP (@eqP _ _ _)) in H
  | |- context [ is_true (negb (@eq_op _ ?x ?y))] =>
     rewrite <- (rwP (@eqP _ x y))
  | H : (negb (@eq_op _  _ _)) = true |- _ => move/eqP: H => H
  | |- (negb (@eq_op _  _ _)) = true => apply/eqP
  | H : context [ (negb (@eq_op _ _ _)) = true ] |- _ =>
     rewrite <-  (rwP (@eqP _ _ _)) in H
  | |- context [ (negb (@eq_op _ ?x ?y)) = true ] =>
     rewrite <- (rwP (@eqP _ x y))

  | H : (leq _ _) = true |- _ => move/leP: H => H
  | H : context [ (leq ?a ?b) = true] |- _ =>
     rewrite <- (rwP (@leP a b)) in H
  | |- (leq _ _) = true => apply/leP
  | |- context [(leq ?a ?b) = true] => rewrite <- (rwP (@leP a b))
  (* Boolean equality *)
  | H : (@eq_op _ _ _) = true |- _ => move/eqP: H => H
  | |- (@eq_op _ _ _) = true => apply/eqP
  | H : context [(@eq_op _ _ _) = true] |- _ =>
     rewrite <-  (rwP (@eqP _ _ _)) in H
  | |- context [(@eq_op _ ?x ?y) = true] => rewrite <- (rwP (@eqP _ x y))

  (* Negated lt *)
  | H : is_true (negb (leq (S _) _)) |- _ => move: H; rewrite -leqNgt=> H
  | H : context [ is_true (negb (leq (S _) _))] |- _ =>
     rewrite -leqNgt in H
  | |- is_true (negb (leq (S _) _)) => rewrite -leqNgt
  | |- context [ is_true (negb (leq (S _) _))] => rewrite -leqNgt

  (* Negated leq *)
  | H : is_true (negb (leq _ _)) |- _ => move: H; rewrite -ltnNge=> H
  | H : context [ is_true (negb (leq _ _))] |- _ =>
     rewrite -ltnNge in H
  | |- is_true (negb (leq _ _)) => rewrite -ltnNge
  | |- context [ is_true (negb (leq _ _))] => rewrite -ltnNge

   (* = flase *)
  | H : (_ = false) |- _ => move/negbT: H => H
  | |- (_ = false) => apply/negP
  | H : context [ (?a = false)] |- _ =>
     rewrite <-  (rwP (@negP a)) in H
  | |- context [ ?a = false] =>
     rewrite <- (rwP (@negP a))

 end.


(* Converting ssrnat operation to their std lib analogues *)
Ltac ssrnatify_op :=
 match goal with
  (* subn -> minus *)
  | H : context [subn _ _] |- _ => rewrite -!minusE in H
  | |- context [subn _ _] => rewrite -!minusE
  (* addn -> plus *)
  | H : context [addn _ _] |- _ => rewrite -!plusE in H
  | |- context [addn _ _] => rewrite -!plusE
  (* muln -> mult *)
  | H : context [muln _ _] |- _ => rewrite -!multE in H
  | |- context [muln _ _] => rewrite -!multE
 end.

(* Preparing a goal to be solved by lia by translating every formula *)
(* in the context or the conclusion which expresses a constraint on *)
(* some nat into the std lib, Prop, analogues *)
Ltac ssrnatify :=
  repeat progress ssrnatify_rel;
  repeat progress ssrnatify_op.

(* Preprocessing + lia *)
Ltac ssrnatlia := try (move=> * //=); do [ ssrnatify; lia | exfalso; ssrnatify; lia].

(***** Intro pattern ltac views *****)
(* This is due to Cyril Cohen.
   TODO: remove when https://github.com/math-comp/math-comp/pull/501 is merged *)

Module Export ipat.

Notation "'[' '1' '!' rules ']'"     := (ltac:(rewrite rules))
  (at level 0, rules at level 200, only parsing) : ssripat_scope.
Notation "'[' '!' rules ']'"         := (ltac:(rewrite !rules))
  (at level 0, rules at level 200, only parsing) : ssripat_scope.
Notation "'[' '-!' rules ']'"         := (ltac:(rewrite -!rules))
  (at level 0, rules at level 200, only parsing) : ssripat_scope.
Notation "'[' 'apply' ']'" := (ltac:(let f := fresh "_top_" in move=> f {}/f))
  (at level 0, only parsing) : ssripat_scope.
 (* we try to preserve the naming by matching the names from the goal *)
(* we do move to perform a hnf before trying to match                *)
Notation "'[' 'swap' ']'" := (ltac:(move;
  lazymatch goal with
  | |- forall (x : _), _ => let x := fresh x in move=> x; move;
    lazymatch goal with
    | |- forall (y : _), _ => let y := fresh y in move=> y; move: y x
    | |- let y := _ in _ => let y := fresh y in move=> y; move: @y x
    | _ => let y := fresh "_top_" in move=> y; move: y x
    end
  | |- let x := _ in _ => let x := fresh x in move => x; move;
    lazymatch goal with
    | |- forall (y : _), _ => let y := fresh y in move=> y; move: y @x
    | |- let y := _ in _ => let y := fresh y in move=> y; move: @y @x
    | _ => let y := fresh "_top_" in move=> y; move: y x
    end
  | _ => let x := fresh "_top_" in let x := fresh x in move=> x; move;
    lazymatch goal with
    | |- forall (y : _), _ => let y := fresh y in move=> y; move: y @x
    | |- let y := _ in _ => let y := fresh y in move=> y; move: @y @x
    | _ => let y := fresh "_top_" in move=> y; move: y x
    end
  end))
  (at level 0, only parsing) : ssripat_scope.
 (* we try to preserve the naming by matching the names from the goal *)
(* we do move to perform a hnf before trying to match                *)
Notation "'[' 'dup' ']'" := (ltac:(move;
  lazymatch goal with
  | |- forall (x : _), _ =>
    let x := fresh x in move=> x;
    let copy := fresh x in have copy := x; move: copy x
  | |- let x := _ in _ =>
    let x := fresh x in move=> x;
    let copy := fresh x in pose copy := x;
    do [unfold x in (value of copy)]; move: @copy @x
  | |- _ =>
    let x := fresh "_top_" in move=> x;
    let copy := fresh "_top" in have copy := x; move: copy x
  end))
  (at level 0, only parsing) : ssripat_scope.
 End ipat.

(****** Hints to deal with dummy bolean goals ******)

Lemma orbTb a b : [|| a, true | b].
Proof. by case: a. Qed.

Lemma orbbT a b : [|| a, b | true].
Proof. by rewrite !orbT. Qed.

Lemma orbbbT a b c: [|| a, b, c | true].
Proof. by rewrite !orbT. Qed.

Lemma orbbbbT a b c d: [|| a, b, c, d | true].
Proof. by rewrite !orbT. Qed.

Hint Resolve orbT orbTb orbbT orbbbT orbbbbT : core.

(* ************************************************************************** *)
(*     Mapping using proof of membership                                      *)
(* ************************************************************************** *)

Section SeqIn.

Context {T : eqType}.
Implicit Type s : seq T.
  
Fixpoint seq_in_sub s s' (sub : subseq s' s) : seq {x in s} :=
  (if s' is h :: t then
     fun sub => 
       exist _ h (mem_subseq sub (mem_head h t)) ::
       seq_in_sub (subseq_trans (subseq_cons t h) sub)
   else fun => [::]
  ) sub.

Definition seq_in s : seq {x in s} := seq_in_sub (subseq_refl s). 

Lemma val_seq_in_sub s s' (sub : subseq s' s) :
  map val (seq_in_sub sub) = s'.
Proof. by elim: s'=> //= ?? IHs in sub *; rewrite IHs. Qed.

Lemma val_seq_in s :
  map val (seq_in s) = s.
Proof. by rewrite /seq_in val_seq_in_sub. Qed.

Lemma seq_in_subE s s' (sub : subseq s' s) :
  seq_in_sub sub = pmap insub s'.
Proof. by rewrite -[in RHS](@val_seq_in_sub s s') map_pK //; apply: valK. Qed.

Lemma seq_inE s :
  seq_in s = pmap insub s.
Proof. by rewrite /seq_in seq_in_subE. Qed.

Lemma seq_in_mem s x (p : x \in s) :
  exist _ x p \in seq_in s.
Proof. by rewrite seq_inE mem_pmap_sub. Qed.

End SeqIn.


(* ************************************************************************** *)
(*     Missing definitions, notations and lemmas for Relation Algebra         *)
(* ************************************************************************** *)

(** Enable rewriting of [lattice.leq] and [weq] using Ssreflect's rewrite tactic *)
Global Instance leq_rewrite_relation ops : 
  RewriteRelation (@lattice.leq ops).
Qed.

Global Instance weq_rewrite_relation ops : 
  RewriteRelation (@lattice.weq ops).
Qed.

(* ************************************************************************** *)
(*     Cartesian product for lattice-valued functions                         *)
(* ************************************************************************** *)

Section CartesianProd.

Context {T : Type} {L : lattice.ops}.

Definition cart_prod (p q : T -> L) : T -> T -> L :=
  fun x y => p x ⊓ q y.

End CartesianProd.

Notation "p × q" := (cart_prod p q) (at level 60, no associativity) : ra_terms.

(* ************************************************************************** *)
(*     Reflexive closure                                                      *)
(* ************************************************************************** *)

Notation "r ^?" := (1 ⊔ r) (left associativity, at level 5, format "r ^?"): ra_terms.

Lemma itr_qmk `{laws} `{BKA ≪ l} n (x: X n n) :
  x^+^? ≡ x^?^+.
Proof. ka. Qed.

(* ************************************************************************** *)
(*     Subtraction (for complemented lattices, i.e. lattices with negation)   *)
(* ************************************************************************** *)

Notation "x \ y" := (x ⊓ !y) (left associativity, at level 45): ra_terms.

Section SubtractionTheory.

Context `{monoid.laws} (n : ob X).
Implicit Types (x : X n n). 

(* TODO: introduce a class of lattices/kleene-algebras 
 *   with decidable equality? *)
Context (eq_dec : 1 ⊔ !1 ≡ (top : X n n)).

(* TODO: reformulate in terms of reflexive closure once 
 *   we'll generalize it to arbitary lattices with identity.
 *)
Lemma qmk_sub_one `{CUP+CAP+TOP ≪ l} x :
  (x \ 1)^? ≡ x^?.
Proof. 
  apply/weq_spec; split; first by lattice.
  by rewrite -[x in _ + x]capxt -eq_dec capcup; lattice.
Qed.

End SubtractionTheory. 

(* ************************************************************************** *)
(*     Morphism instance for pointwise construction on lattices               *)
(* ************************************************************************** *)

Section PWMorph.

Context {h l : level}.
Context {X Y : lattice.ops}.
Context {L : lattice.laws h Y}.
Context {Hl : l ≪ h}.

Universe pw. 

Context {Z : Type@{pw}}.

Instance pw_morph (f : X -> Y) :
  @morphism l X Y f -> @morphism l (pw_ops X Z) (pw_ops Y Z) (fun g => f \o g).
Proof.
  move=> Hm; constructor; simpl.
  - by move=> x y H a /=; apply: fn_leq. 
  - by move=> x y H a /=; apply: fn_weq. 
  - by move=> ? x y a /=; apply: fn_cup. 
  - by move=> ? x y a /=; apply: fn_cap. 
  - by move=> ? x /=; apply: fn_bot. 
  - by move=> ? x /=; apply: fn_top. 
  - by move=> ? x a /=; apply: fn_neg. 
Qed.

End PWMorph.

(* ************************************************************************** *)
(*     Instance of Lattice and KAT for decidable realtions                    *)
(* ************************************************************************** *)

(* Adopted from relation-algebra/fhrel.v  *)

Section DHRelType.
  Variables A B : eqType.
  Definition dhrel_type := A -> B -> bool.
  Definition dhrel_of of phant A & phant B := dhrel_type.
End DHRelType.

Notation "{ 'dhrel' A & B }" := (dhrel_of (Phant A) (Phant B))
  (at level 0, format "{ 'dhrel'  A  &  B }") : type_scope.

Section DHRel.
Implicit Types A B : eqType.

(* Lattice structure is derived via the powerset
 * construction on the lattice of booleans. 
 *)

Canonical Structure dhrel_lattice_ops A B := 
  lattice.mk_ops {dhrel A & B} lattice.leq weq cup cap neg bot top.

Arguments lattice.leq : simpl never.
Arguments lattice.weq : simpl never.

Global Instance dhrel_lattice_laws A B : 
  lattice.laws BDL (dhrel_lattice_ops A B) := 
    lower_lattice_laws (H:=pw_laws _).
  (* lattice.laws (BL+ONE+CNV) (dhrel_lattice_ops A B) :=  *)
  (*   lower_lattice_laws (H:=pw_laws _). *)

Section MonoidOps.
Variables (A B C : eqType).

Definition dhrel_one : {dhrel A & A} := 
  @eq_op A.

Definition dhrel_cnv (r : {dhrel A & B}) : {dhrel B & A} := 
  fun x y => r y x.

Definition dhrel_inj (p : pred A) := 
  fun x y => (x == y) && p x.

Definition dhrel_dot (r1 : {dhrel A & B}) (r2 : {dhrel B & C}) : {dhrel A & C} :=
  fun x y => false.
Definition dhrel_ldv (r1 : {dhrel A & B}) (r2 : {dhrel A & C}) : {dhrel B & C} :=
  fun x y => false.
Definition dhrel_rdv (r1 : {dhrel B & A}) (r2 : {dhrel C & A}) : {dhrel C & B} :=
  fun x y => false.

Definition dhrel_itr (r : {dhrel A & A}) : {dhrel A & A} := 
  fun x y => false.
Definition dhrel_str (r : {dhrel A & A}) : {dhrel A & A} := 
  fun x y => false.

End MonoidOps.

Canonical dhrel_monoid_ops := 
  monoid.mk_ops eqType dhrel_lattice_ops
                dhrel_dot
                dhrel_one
                dhrel_itr
                dhrel_str
                dhrel_cnv
                dhrel_ldv
                dhrel_rdv.

(** Ensure that the [dhrel_*] definitions simplify, given enough arguments. *)
Arguments dhrel_dot {_ _ _} _ _ /.
Arguments dhrel_cnv {_ _} _ _ /.
Arguments dhrel_one {_} _ _ /.
Arguments dhrel_str {_} _ _ /.
Arguments dhrel_ldv {_} _ _ /.
Arguments dhrel_rdv {_} _ _ /.
Arguments dhrel_inj {_} _ _ _ /.

(** We obtain the monoid laws using a faithful functor to the hrel model *)
Definition hrel_of (A B : eqType) (r : {dhrel A & B}) : hrel A B := fun x y => r x y.
Ltac hrel_prop := do ! move => ?; rewrite /hrel_of /=; to_prop; by firstorder.

Lemma hrel_of_morphism (A B : eqType) : 
  morphism BDL (@hrel_of A B).
  (* morphism (BDL+ONE+CNV) (@hrel_of A B). *)
Proof.
  split; try done; try hrel_prop.
  move => e1 e2 H x y. apply/eq_bool_iff. exact: H.
Qed.

(* We cannot declare the monoid laws instance, since 
 * we cannot define composition on `dhrel` structure.
 * The current design of relation-algebra package 
 * does not allow an optional composition operation. 
 * This requires a custom fork:
 * git+https://github.com/eupp/relation-algebra#monoid-decoupling
 * However, maintaining the custom fork seems to be a bit complicated task, 
 * therefore we postpone it (we hope it will be merged eventually). 
 * Despite we cannot declare monoid laws instance 
 * (and thus we cannot use some lemmas from relation-algebra)
 * we still can use notations.
 *)

(* Lemma hrel_of_functor : functor (BDL+ONE+CNV) hrel_of. *)
(* Proof. *)
(*   apply (@Build_functor (BDL+ONE+CNV) dhrel_monoid_ops hrel_monoid_ops id hrel_of). *)
(*   all: try done. all: try hrel_prop. *)
(*   apply: hrel_of_morphism. *)
(* Qed. *)

(* Lemma dhrel_monoid_laws_BDL: monoid.laws (BDL+ONE+CNV) dhrel_monoid_ops. *)
(* Proof. *)
(*   eapply (laws_of_faithful_functor hrel_of_functor) => //. *)
(*   move => A B e1 e2 H x y. apply/eq_bool_iff. exact: H. *)
(* Qed. *)

(* Global Instance dhrel_monoid_laws: monoid.laws (BL+ONE+CNV) dhrel_monoid_ops. *)
(* Proof. *)
(*   case dhrel_monoid_laws_BDL => *. *)
(*   split; try assumption. exact: dhrel_lattice_laws. *)
(* Qed. *)

Lemma dhrel_oneE A a b : (1 : {dhrel A & A}) a b = (a == b).
Proof. reflexivity. Qed.
Definition oneE := (hrel_oneE,fhrel_oneE).

(* The following is required, see fhrel.v for details *)
Definition d_top_def (A B : eqType) of phant A & phant B := 
  (@top (@mor dhrel_monoid_ops A B)).
Notation d_top A B := (d_top_def (Phant A) (Phant B)).

Definition d_zero_def (A B : eqType) of phant A & phant B := 
  (@bot (@mor dhrel_monoid_ops A B)).
Notation d_zero A B := (d_zero_def (Phant A) (Phant B)).

Definition d_one_def (A : eqType) of phant A := 
  (@one dhrel_monoid_ops A).
Notation d_one A := (d_one_def (Phant A)).

Arguments d_top_def A B /.
Arguments d_zero_def A B /.
Arguments d_one_def A /.

Definition dset : ob dhrel_monoid_ops -> lattice.ops := pw_ops bool_lattice_ops.

Canonical Structure dhrel_kat_ops := 
  kat.mk_ops dhrel_monoid_ops dset (@dhrel_inj).

(* Same issue as for monoid laws instance (see above). *)

(* Global Instance dhrel_kat_laws: kat.laws (CUP+BOT+ONE) BL dhrel_kat_ops. *)
(* Proof. *)
(*   split. *)
(*   - by eapply lower_laws.  *)
(*   - move => A. by eapply lower_lattice_laws. *)
(*   - move => A. *)
(*     have H : Proper (lattice.leq ==> lattice.leq) (@dhrel_inj A). *)
(*     + move => e1 e2 H x y /=. by case: (_ == _) => //=.  *)
(*     split => //=. *)
(*     + move => x y. rewrite !weq_spec. by intuition. *)
(*     + move => _ f g x y /=. by case: (_ == _); case (f x); case (g x). *)
(*     + move => _ x y /=. by rewrite andbF. *)
(*   - move => _ _ A x y /=. by rewrite andbT. *)
(*   - move => _ _ A p q x y //=.  *)
(* Qed. *)

Section Theory. 

Context {T : eqType}.

Lemma dhrel_eq_dec : 1 ⊔ !1 ≡ (top : {dhrel T & T}).
Proof. rewrite /weq => x y /=. case: (x =P y)=> //=. Qed.

End Theory.

End DHRel.

(* ************************************************************************** *)
(*     Morphism lemmas for bool/Prop relations.                               *)
(* ************************************************************************** *)

(* The following lemmas are more convinient to work with 
 * than using morphism instances directly. 
 *)

Lemma rel_leq_m {A B : eqType} (r1 r2 : {dhrel A & B}) : 
  r1 ≦ r2 -> (r1 : hrel A B) ≦ (r2 : hrel A B).
Proof. by case (hrel_of_morphism A B)=> H ??????; apply H; solve_lower. Qed.

Lemma rel_weq_m {A B : eqType} (r1 r2 : {dhrel A & B}) : 
  r1 ≡ r2 -> (r1 : hrel A B) ≡ (r2 : hrel A B).
Proof. by case (hrel_of_morphism A B)=> ? H ?????; apply H; solve_lower. Qed.

Lemma rel_cup_m {A B : eqType} (r1 r2 : {dhrel A & B}) : 
  (r1 ⊔ r2 : hrel A B) ≡ (r1 : hrel A B) ⊔ (r2 : hrel A B).
Proof. by case (hrel_of_morphism A B)=> ?? H ????; apply H; solve_lower. Qed.

Lemma rel_cap_m {A B : eqType} (r1 r2 : {dhrel A & B}) : 
  (r1 ⊓ r2 : hrel A B) ≡ (r1 : hrel A B) ⊓ (r2 : hrel A B).
Proof. by case (hrel_of_morphism A B)=> ??? H ???; apply H; solve_lower. Qed.

Lemma rel_bot_m {A B : eqType} : 
  ((bot : {dhrel A & B}) : hrel A B) ≡ (bot : hrel A B).
Proof. by case (hrel_of_morphism A B)=> ???? H ??; apply H; solve_lower. Qed.

Lemma rel_top_m {A B : eqType} : 
  ((top : {dhrel A & B}) : hrel A B) ≡ (top : hrel A B).
Proof. by case (hrel_of_morphism A B)=> ????? H ?; apply H; solve_lower. Qed.

Lemma rel_neg_m {A B : eqType} (r : {dhrel A & B}) : 
  (!r : hrel A B) ≡ !(r : hrel A B).
Proof. move=> x y /=. split. apply /elimN/idP. apply /introN/idP. Qed.

Lemma rel_sub_m {A B : eqType} (r1 r2 : {dhrel A & B}) : 
  (r1 \ r2 : hrel A B) ≡ (r1 : hrel A B) \ (r2 : hrel A B).
Proof. by rewrite -rel_neg_m rel_cap_m. Qed.

Lemma rel_one_m {A : eqType} : 
  ((1 : {dhrel A & A}) : hrel A A) ≡ (1 : hrel A A).
Proof. do ! move => ?; rewrite /hrel_of /=; to_prop; by firstorder. Qed.
(* Proof. case hrel_of_functor=> ?? H ?????; apply H; solve_lower. Qed. *)

Lemma rel_qmk_m {A : eqType} (r : {dhrel A & A}) : 
  (r^? : hrel A A) ≡ (r : hrel A A)^?. 
Proof. by rewrite rel_cup_m rel_one_m. Qed.

Lemma rel_cnv_m {A : eqType} (r : {dhrel A & A}) : 
  (r° : hrel A A) ≡ (r : hrel A A)°.
Proof. do ! move => ?; rewrite /hrel_of /=; to_prop; by firstorder. Qed.
(* Proof. case hrel_of_functor=> ????? H ??; apply H; solve_lower. Qed. *)

(* ************************************************************************** *)
(*     Missing opportunities for rewriting                                    *)
(* ************************************************************************** *)

Instance hrel_neg_leq {A B : Type} : 
  Proper ((@leq (hrel_lattice_ops A B)) --> (@leq (hrel_lattice_ops A B))) neg.
Proof. rewrite /leq=> x y /= H a b; apply /contra_not/H. Qed.

Instance hrel_neg_weq {A B : Type} : 
  Proper (@weq (hrel_lattice_ops A B) ==> (@weq (hrel_lattice_ops A B))) neg.
Proof. 
  rewrite /weq=> x y /= H a b. 
  move: (H a b)=> [Hl Hr]; split; by apply /contra_not.
Qed.

(* ************************************************************************** *)
(*     Connecting reflection lemmas with pointwise equivalence                *)
(* ************************************************************************** *)

Section PwEqvReflect.

Context {T : eqType}.
Implicit Types (R : relation T) (r : rel T).

(* TODO: introduce `reflect_rel := forall x y, (R x y) (r x y)` ? *)

Lemma weq_reflect R r :
  R ≡ r -> forall x y, reflect (R x y) (r x y).
Proof. move=> H x y; apply: equivP; [exact: idP | symmetry; apply H]. Qed.

Lemma reflect_weq R r :
  (forall x y, reflect (R x y) (r x y)) -> R ≡ r.
Proof. by move=> H x y; apply rwP. Qed.

End PwEqvReflect.

(* ************************************************************************** *)
(*     Reconciling relation-algebra relation closures with vanilla Coq        *)
(* ************************************************************************** *)

Hint Resolve r_refl rt_refl : core.

Section RelAux.

Context {T : Type}.
Implicit Types (R : hrel T T) (r : rel T).

(* TODO: consider to reformulate it in terms of relation-algebra 
 * (or try to just use kat tactics inplace) 
 *)
Lemma clos_t_clos_rt R x y :
  clos_trans T R x y -> clos_refl_trans T R x y.
Proof.
  elim=> [|???? H ??]; first by constructor.
  by apply: rt_trans H _.
Qed.

Lemma clos_refl_transE R :
  clos_refl_trans T R ≡ clos_refl T (clos_trans T R).
Proof.
  move=> x y; split.
  - elim=> [{}x {}y xy | {}x | {}x {}y z _ xy _ yz] //.
    - by apply/r_step/t_step.
    - case: xy yz=> [{}y xy [{}z yz|] |] //=; last by apply r_step.  
      apply/r_step/t_trans; [exact: xy| exact: yz].
  case=> // ?; elim=> [|???? H ??]; first by constructor. 
  by apply: rt_trans H _.
Qed.

Lemma clos_refl_hrel_qmk R :
  clos_refl T R ≡ R^?.
Proof.
  split; first by case; [right | left].
  case=> [->|]; first exact: r_refl; exact: r_step.
Qed.

Lemma clos_trans_1n_hrel_itr R :
  clos_trans_1n _ R ≡ R^+.
Proof.
  move=> x y; split.
  - elim=> {x y} [x y | x z y] Rxy; first by exists y=> //; exists O.
    by move=> ? [z' H' [n it]]; exists z=> //; exists n.+1, z'.
  case=> z xz [n]; elim: n x z xz => [x z xz <-| n IHn x z xz /=].
  - by apply/t1n_step.
  case=> w zw /IHn - /(_ z zw) ct_zy.
  by apply: Relation_Operators.t1n_trans xz ct_zy.
Qed.

Lemma clos_trans_hrel_itr R :
  clos_trans _ R ≡ R^+.
Proof.
  move=> x y; rewrite clos_trans_t1n_iff.
  by apply: clos_trans_1n_hrel_itr.
Qed.

Lemma clos_refl_trans_hrel_str R : 
  clos_refl_trans _ R ≡ R^*. 
Proof. by rewrite str_itr clos_refl_transE clos_refl_hrel_qmk clos_trans_hrel_itr. Qed.

End RelAux.

Lemma exists_equiv {T} {A B : T -> Prop} :
  (forall x, A x <-> B x) -> (exists x, A x) <-> (exists x, B x).
Proof. move=> H; split=> [][] x /H ?; by exists x. Qed.

Inductive and6 (P1 P2 P3 P4 P5 P6 : Prop) : Prop :=
  And6 of P1 & P2 & P3 & P4 & P5 & P6.

Notation "[ /\ P1 , P2 , P3 , P4 , P5 & P6 ]" :=
  (and6 P1 P2 P3 P4 P5 P6) : type_scope.

Section ReflectConnectives.

Variable b1 b2 b3 b4 b5 b6 : bool.

Lemma and6P : reflect [/\ b1, b2, b3, b4, b5 & b6] [&& b1, b2, b3, b4, b5 & b6].
Proof.
  by case: b1; case: b2; case: b3; case: b4; case: b5; case: b6;
    constructor; try by case.
Qed.

End ReflectConnectives.

Section RelationOnSeq.

Lemma rfoldl {A B C D} (r : A -> C -> bool) (r' : B -> D -> bool) 
  (f : A -> B -> A) (f' : C -> D -> C) (bs : seq B) (ds : seq D)
  (ini : A) (ini' : C) : r ini ini' ->
  (forall a b c d, r a c -> r' b d -> r (f a b) (f' c d)) ->
  all2 r' bs ds -> r (foldl f ini bs) (foldl f' ini' ds).
Proof.
  move=> + H.
  elim: bs ini ini' ds=> [??[]//|?? IHbs ?? []//= ??? /andP[*]].
  by apply/IHbs; first exact/H.
Qed.

Lemma rpath {T S} (sf : T -> S -> bool)  (r' : rel S) (y : S)
  (s : seq S) (r : rel T) (t : seq T) (x : T) : sf x y ->
  (forall a b c d, sf a c -> sf b d -> r a b = r' c d) ->
  all2 sf t s -> 
  path r x t = path r' y s.
Proof.
  move=> + H.
  elim: t x y s=> [??[]//|/=> IHt ?? []//=> /H R /andP[/[dup] /IHt IH+/IH]].
  by move/R->=>->.
Qed.

End RelationOnSeq.

Section Swap.

Context {T : eqType}.

Section SwapDef.

Context (f : T -> T) (a b : T).

Definition swap := fun x =>
  if x == a then
    f b
  else if x == b then 
    f a
  else f x.

Lemma swap1: swap a = f b.
Proof. by rewrite /swap eq_refl. Qed.

Lemma swap2: swap b = f a.
Proof. by rewrite /swap eq_refl; case: ifP=> // /eqP->. Qed.

Lemma swap_not_eq x: x != a -> x != b -> f x = swap x.
Proof. by rewrite /swap=> /negbTE->/negbTE->. Qed.

End SwapDef.

Lemma swapxx x f : swap f x x =1 f.
Proof. by move=> y; rewrite /swap eq_sym; case: (x =P y)=> [->|]. Qed.

Lemma swap_inv a b: involutive (swap id a b).
Proof.
  move=> ?; rewrite {2}/swap; case: ifP=> [/eqP->|]; first exact/swap2.
  move/negbT=> ?; case: ifP=> [/eqP->|/negbT ?]; first exact/swap1.
  exact/esym/swap_not_eq.
Qed.


Lemma bij_swap a b f : bijective f -> bijective (swap f a b).
Proof.
  move=> /[dup] bi [g c1 c2].
  apply/(@Bijective _ _ _ (swap g (f a) (f b)))=> x; rewrite /swap.
  - case: (x =P a)=> [->|]; rewrite ?eq_refl ?c1 ?bij_eq //.
    - by case: ifP=> // /eqP.
    case: (x =P b)=> [->|]; first by rewrite ?eq_refl.
    by rewrite ?bij_eq // => /eqP/negbTE->/eqP/negbTE->.
  case: (x =P f a)=>[->|]; rewrite ?c1 ?eq_refl; first by case: ifP=>[/eqP->|].
  case: (x =P f b)=>[->|]; rewrite ?eq_refl // -?[g x == _](bij_eq bi) c2.
  by move/eqP/negbTE->=>/eqP/negbTE->.
Qed.


End Swap.

Section OptionUtils. 

Context {T rT : Type}.

Definition opreim (f : T -> option rT) (p : pred rT) : simpl_pred T := 
  [pred x | match f x with Some x => p x | _ => false end]. 

Definition orelpre (f : T -> option rT) (r : rel rT) : simpl_rel T := 
  [rel x y | match f x, f y with Some x, Some y => r x y | _, _ => false end].

End OptionUtils.