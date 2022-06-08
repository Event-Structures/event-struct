From Coq Require Import Relations Relation_Operators.
From RelationAlgebra Require Import lattice monoid rel kat_tac.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat zify. 
From mathcomp Require Import eqtype choice seq order path.
From mathcomp Require Import fintype finfun fingraph finmap.
From mathcomp.tarjan Require Import extra acyclic kosaraju acyclic_tsorted. 
From eventstruct Require Import utils seq rel_algebra rel inhtype ident.

(******************************************************************************)
(* A theory of finitely supported graphs.                                     *)
(* TODO.                                                                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope rel_scope.
Local Open Scope fset_scope.
Local Open Scope ident_scope.

Declare Scope fsgraph_scope.
Delimit Scope fsgraph_scope with fsgraph.

Local Open Scope fsgraph_scope.

Module FsGraph.

Module Export Def.
Section hDef.
Context (T U : identType).

(* TODO: ideogically it would be better to make the definition opaque, 
 *   i.e. to keep internal graph representation hidden. 
 *   However, by making fset-based representation transparent 
 *   we can easily reuse all the fset infrastructure 
 *   (e.g. unions, intersections, etc)
 *   without the need to write a lot of boilerplate code. 
 *   In the future, however, we should find a better solution. 
 *   For example by developing some common theory of set-like structures?
 *)
Definition hfsgraph := {fset T * U}.

Implicit Types (g : hfsgraph).

Coercion hrel_of_hfsgraph g : {hrel T & U} := 
  fun x y => (x, y) \in g.

Definition hfsgraph_apply g : T -> U -> bool := hrel_of_hfsgraph g.
Coercion hfsgraph_apply : hfsgraph >-> Funclass.

Definition dom g : {fset T} := [fset (fst p) | p in g].
Definition cod g : {fset U} := [fset (snd p) | p in g].

(* TODO: move to theory module *)

Lemma fsgraphE g x y : (g x y) = ((x, y) \in g).
Proof. done. Qed.

Lemma dom_cod_restr g : 
  (g : {hrel T & U}) \<= mem (dom g) \x mem (cod g).
Proof. 
  move=> x y /=; rewrite /le_bool /dom /cod /=. 
  rewrite /hrel_of_hfsgraph=> ing. 
  by apply/andP; split; apply/imfsetP; exists (x, y).
Qed.

End hDef.

Notation fsgraph T := (@hfsgraph T T).

Definition fsgraph0 {T U} : hfsgraph T U := fset0.

Section Def.
Context {T : identType}.
Implicit Types (g : fsgraph T).

Definition fld g : {fset T} := dom g `|` cod g.

Lemma fld_restr g : 
  (g : {hrel T & T}) \<= mem (fld g) \x mem (fld g).
Proof. 
  move=> x y /dom_cod_restr /= /andP[].
  by rewrite /fld !inE=> -> -> /=.
Qed.

End Def.
End Def.

Module Export Syntax. 
Notation "[ 'emp' ]" := (fsgraph0)
  (at level 0, format "[ 'emp' ]") : fsgraph_scope.
End Syntax.

Module Export Hom.
Section Def. 
Context {T U : identType}.
Implicit Types (f : T -> U).
Implicit Types (g : fsgraph T) (h : fsgraph U).

Definition hom f g h := {homo f : x y / g x y >-> h x y}.

Definition hom_le g h := 
  let (fT, fU) := (fld g, fld h) in
  [exists f : {ffun fT -> fU}, 
    [forall x, forall y, (g (val x) (val y)) ==> h (val (f x)) (val (f y))]
  ].

End Def.

Section hTheory.
Context {T U : identType}.
Implicit Types (f : T -> U).
Implicit Types (g : fsgraph T) (h : fsgraph U).

Lemma hom_emp f h : hom f [emp] h.
Proof. done. Qed.

(* Lemma fld_emp g :  *)
(*   (g == [emp]) = (fld g == fset0). *)
(* Proof. admit. Admitted. *)

Lemma hom_dom f g h x : 
  hom f g h -> x \in dom g -> f x \in dom h.
Proof. 
  move=> homf /imfsetP /= [[_ y]] /[swap] /= <- Hin.
  apply/imfsetP=> /=; exists (f x, f y)=> //=; exact/homf.
Qed.

Lemma hom_cod f g h y : 
  hom f g h -> y \in cod g -> f y \in cod h.
Proof. 
  move=> homf /imfsetP /= [[x _]] /[swap] /= <- Hin.
  apply/imfsetP=> /=; exists (f x, f y)=> //=; exact/homf.
Qed.

Lemma hom_fld f g h x : 
  hom f g h -> x \in fld g -> f x \in fld h.
Proof. 
  move=> homf; rewrite /fld !inE. 
  by move=> /orP[/(hom_dom homf) | /(hom_cod homf)] ->.
Qed.

Lemma hom_leP g h :
  reflect (exists f, hom f g h) (hom_le g h).
Proof.
  apply/(equivP existsP); split=> /=; last first.
  - move=> [f] homf.
    pose ff : {ffun (fld g) -> (fld h)} := 
      [ffun x => Sub (f (val x)) (hom_fld homf (valP x))].
    exists ff; apply/forall2P=> /= x y; apply/implyP. 
    rewrite !ffunE /=; exact/homf.
  move=> [ff] /homo2P homf. 
  pose f : T -> U := 
    fun x => odflt \i0 (omap (val \o ff) (insub x)).
  exists f => /= x y; rewrite /f. 
  move=> /[dup] /fld_restr /= /andP[xin yin].
  rewrite !insubT /= => gxy; exact/homf.
Qed.  

End hTheory.

End Hom.
End Hom.

Section KleeneAlgebra.
Context {T U : choiceType}.

Canonical Structure fsgraph_lattice_ops : lattice.ops := {|
  lattice.car := @hfsgraph T U;
  lattice.leq := fsubset;
  lattice.weq := eq_op;
  lattice.cup := fsetU;
  lattice.cap := fsetI;
  lattice.neg := (fun _ => fset0);
  lattice.bot := fset0;
  lattice.top := fset0;
|}.

Lemma hrel_of_hfsgrpa_morph : 
  lattice.morphism (CUP+CAP+BOT) hrel_of_hfsgraph.
Proof.
  split; try done.
  - by move=> ?? /fsubsetP subs ?? /= /subs.
  - by move=> ?? /eqP ->.
  all: by move=> ??? /= ?? /=; rewrite /hrel_of_hfsgraph inE. 
Qed.

End KleeneAlgebra.

End FsGraph.

