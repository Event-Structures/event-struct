From Coq Require Import Relations.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun eqtype.
From mathcomp Require Import seq path fingraph fintype.
From mathcomp.tarjan Require Import extra acyclic kosaraju acyclic_tsorted.
From RelationAlgebra Require Import lattice monoid boolean rel fhrel.
From RelationAlgebra Require Import kleene kat_tac.

(* ************************************************************************** *)
(*   Missing definitions, notations and lemmas for relation-algebra package   *)
(* ************************************************************************** *)

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Unset Strict Implicit.

(* ************************************************************************** *)
(*     Utilities                                                              *)
(* ************************************************************************** *)

Section PropUtils.
Context {T : Type}.
Implicit Types (P : T -> Prop).

Lemma inh_nempty P :
  inhabited { x | P x } -> ~ (P ≦ bot).
Proof. by move=> [] [] x Hx H; move: (H x Hx)=> //=. Qed.

End PropUtils.

(* ************************************************************************** *)
(*     Cartesian product for lattice-valued functions                         *)
(* ************************************************************************** *)

Section Prod.
Context {T : Type} {L : lattice.ops}.

Definition cart_prod (p q : T -> L) : T -> T -> L :=
  fun x y => p x ⊓ q y.

End Prod.

Notation "p × q" := (cart_prod p q) (at level 60, no associativity) : ra_terms.

(* ************************************************************************** *)
(*     Reflexive closure                                                      *)
(* ************************************************************************** *)

Notation "r ^?" := (1 ⊔ r) (left associativity, at level 5, format "r ^?"): ra_terms.

Lemma itr_qmk `{laws} `{BKA ≪ l} n (x : X n n) :
  x^+^? ≡ x^?^+.
Proof. by ka. Qed.

(* TODO: make lemma instance of Proper for rewriting? *)
Lemma qmk_weq `{laws} `{CUP ≪ l} n (x y : X n n):
  x ≡ y -> x^? ≡ y^?.
Proof. by move => ->. Qed.

Lemma qmk_str `{laws} `{BKA ≪ l} n (x : X n n) :
  x^*^? ≡ x^*.
Proof. ka. Qed.

(* ************************************************************************** *)
(*     Subtraction (for complemented lattices, i.e. lattices with negation)   *)
(* ************************************************************************** *)

Notation "x \ y" := (x ⊓ !y) (left associativity, at level 45): ra_terms.

Section SubtractionTheory.

Context `{monoid.laws} (n : ob X).
Implicit Types (x : X n n).

(* TODO: introduce a class of lattices/KATs with decidable equality? *)
Hypothesis (eq_dec : 1 ⊔ !1 ≡ (top : X n n)).

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
 * However, maintaining the custom fork seems to be a bit of a complicated task,
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

(* The following lemmas are more convenient to work with
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

#[export] Hint Resolve r_refl rt_refl : core.

Arguments clos_refl [A] R x y.
Arguments clos_trans [A] R x y.
Arguments clos_trans_1n [A] R x y.
Arguments clos_trans_n1 [A] R x y.
Arguments clos_refl_trans [A] R x y.

Section RelClos.

Context {T : Type}.
Implicit Types (R : hrel T T) (r : rel T).

(* TODO: consider to reformulate it in terms of relation-algebra
 * (or try to just use kat tactics inplace)
 *)
Lemma clos_t_rt R x y :
  clos_trans R x y -> clos_refl_trans R x y.
Proof.
  elim=> [|???? H ??]; first by constructor.
  by apply: rt_trans H _.
Qed.

Lemma clos_rt_crE R :
  clos_refl_trans R ≡ clos_refl (clos_trans R).
Proof.
  move=> x y; split.
  - elim=> [{}x {}y xy | {}x | {}x {}y z _ xy _ yz] //.
    - by apply/r_step/t_step.
    - case: xy yz=> [{}y xy [{}z yz|] |] //=; last by apply r_step.
      apply/r_step/t_trans; [exact: xy| exact: yz].
  case=> // ?; elim=> [|???? H ??]; first by constructor.
  by apply: rt_trans H _.
Qed.

Lemma clos_r_qmk R :
  clos_refl R ≡ R^?.
Proof.
  split; first by case; [right | left].
  case=> [->|]; first exact: r_refl; exact: r_step.
Qed.

Lemma clos_t1n_itr R :
  clos_trans_1n R ≡ R^+.
Proof.
  move=> x y; split.
  - elim=> {x y} [x y | x z y] Rxy; first by exists y=> //; exists O.
    by move=> ? [z' H' [n it]]; exists z=> //; exists n.+1, z'.
  case=> z xz [n]; elim: n x z xz => [x z xz <-| n IHn x z xz /=].
  - by apply/t1n_step.
  case=> w zw /IHn - /(_ z zw) ct_zy.
  by apply: Relation_Operators.t1n_trans xz ct_zy.
Qed.

Lemma clos_t_itr R :
  clos_trans R ≡ R^+.
Proof.
  move=> x y; rewrite clos_trans_t1n_iff.
  by apply: clos_t1n_itr.
Qed.

Lemma clos_rt_str R :
  clos_refl_trans R ≡ R^*.
Proof.
  rewrite str_itr clos_rt_crE clos_r_qmk.
  by rewrite clos_t_itr.
Qed.

Lemma itr_prod (D : T -> Prop) :
  (D × D : hrel T T)^+ ≡ D × D.
Proof.
  apply/weq_spec; split; last exact/itr_ext.
  by apply/itr_ind_l1=> //= x y [] z [] ++ [].
Qed.

Lemma clos_t_restr R D :
  R ≦ D × D -> R^+ ≦ D × D.
Proof. move=> rD; rewrite -itr_prod; exact/itr_leq. Qed.

(* TODO: this cannot be proven for KA+NEG,
 *   because hrel does not have NEG
 *)
Lemma str_itr_sub_one R :
  R^* \ 1 ≡ R^+ \ 1.
Proof.
  rewrite str_itr capC capcup.
  suff->: !1 ⊓ (1 : hrel T T) ≡ 0.
  - by lattice.
  by move=> ?? /=; split=> // [[]].
Qed.

(* TODO: also need to reprove this (see qmk_weq),
 *   because of some techinical issues with typeclass inference
 *)
Lemma qmk_weq_rel {U : eqType} (r1 r2 : {dhrel U & U}) :
  r1 ≡ r2 -> r1^? ≡ r2^?.
Proof. by move=> ->. Qed.

End RelClos.


Section FinRel.
Context {T : finType}.
Implicit Types (R : hrel T T) (r : rel T).

Lemma connect_strE r :
  (r : {fhrel T & T})^* ≡ (connect r).
Proof. done. Qed.

Lemma connect_strP r x y :
  reflect ((r : hrel T T)^* x y) (connect r x y).
Proof. by move=> /=; apply/(equivP idP)/connect_iter. Qed.

End FinRel.

(* ************************************************************************** *)
(*     Auxiliary definitions and lemmas about binary relations                *)
(* ************************************************************************** *)

Section RelAux.

Context {T : Type}.
Implicit Types (R : hrel T T) (r : rel T).

Definition minimal R x := forall y, R y x -> x = y.

Definition maximal R x := forall y, R x y -> x = y.

Lemma minimal_maximal R : minimal R ≡ maximal R°.
Proof. by rewrite /cnv /= /hrel_cnv /minimal /maximal. Qed.

(* TODO: relax to `leq` ? *)
Instance minimal_weq :
  Proper (weq ==> weq) minimal.
Proof.
  rewrite /minimal; move=> R1 R2 H x.
  by split; move=> + y /H; move=> /[apply].
Qed.

Instance maximal_weq :
  Proper (weq ==> weq) maximal.
Proof.
  move=> R1 R2. rewrite -!minimal_maximal.
  by move=> /cnv_weq; apply: minimal_weq.
Qed.

Lemma minimal_str R : minimal R ≡ minimal R^*.
Proof.
  move=> s; split=> [/[swap] ? /[swap]|/[swap] s' /(_ s') I /(str_ext R)/I //].
  suff: R^* ≦ (fun s s' => minimal R s' -> s' = s).
  - by move=> /[apply] /[apply].
  apply/str_ind_l1=> ?? // [? ++ /[dup]].
  move=> H /[apply]; move: H=> /[swap] ->.
  by move=> /[swap] /[apply].
Qed.

Lemma maximal_str R : maximal R ≡ maximal R^*.
Proof. by rewrite -!minimal_maximal minimal_str -kleene.cnvstr. Qed.

End RelAux.
