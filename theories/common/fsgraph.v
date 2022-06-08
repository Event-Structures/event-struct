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
Context {T U : identType}.

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

End hDef.

Arguments hfsgraph T U : clear implicits.

Notation fsgraph T := (hfsgraph T T).

Definition fsgraph0 {T U} : hfsgraph T U := fset0.

Section Def.
Context {T U : identType}.
Implicit Types (g : fsgraph T).
Implicit Types (f : T -> U).

Definition fld g : {fset T} := dom g `|` cod g.

Definition fsg_map f g : fsgraph U := 
  (fun '(x, y) => (f x, f y)) @` g.

End Def.
End Def.

Module Export Syntax. 
Notation "[ 'emp' ]" := (fsgraph0)
  (at level 0, format "[ 'emp' ]") : fsgraph_scope.
Notation "f @` g" := (fsg_map f g)
  (at level 24) : fsgraph_scope.
Notation "@! f" := (fun g => f @` g)%fsgraph
  (at level 10, f at level 8, no associativity, format "@!  f") : fsgraph_scope.
End Syntax.

Module Export Theory.
Section Theory.
Context {T U V : identType}.
Implicit Types (g : fsgraph T).

Lemma fsgraphE g x y : (g x y) = ((x, y) \in g).
Proof. done. Qed.

Lemma dom_cod_restr g : 
  g \<= mem (dom g) \x mem (cod g) :> rel T.
Proof. 
  move=> x y /=; rewrite /le_bool /dom /cod /=. 
  rewrite /hrel_of_hfsgraph=> ing. 
  by apply/andP; split; apply/imfsetP; exists (x, y).
Qed.

Lemma fld_restr g : 
  g \<= mem (fld g) \x mem (fld g) :> rel T.
Proof. 
  move=> x y /dom_cod_restr /= /andP[].
  by rewrite /fld !inE=> -> -> /=.
Qed.

Lemma fsg_map_id g : 
  id @` g = g.
Proof. 
  rewrite /fsg_map; apply/fsetP=> /= [[x y]]. 
  apply/idP/idP=> [/imfsetP[[??]] /= ? [-> ->]|] //. 
  by move=> ?; apply/imfsetP; exists (x, y).
Qed.

Lemma fsg_map_comp f (h : U -> V) g : 
  (h \o f) @` g = (@! h \o @! f) g.
Proof.
  rewrite /fsg_map; apply/fsetP=> /= [[x y]]. 
  apply/idP/idP=> /imfsetP /= [[{}x {}y]] + [-> ->] /=.
  - move=> ?; apply/imfsetP; exists (f x, f y)=> //. 
    by apply/imfsetP; exists (x, y).
  move=> /imfsetP /= [[{}x {}y]] /[swap] [[-> ->]] ?. 
  by apply/imfsetP; exists (x, y).
Qed.

End Theory.
End Theory.

Module Export Hom.
Section Def. 
Context {T : identType}.
Implicit Types (f : T -> T) (g h : fsgraph T).

Definition hom f g h := {homo f : x y / g x y >-> h x y}.

Definition fin_hom g h (ff : {ffun (fld g) -> (fld h)}) := 
  [forall x, forall y, (g (val x) (val y)) ==> h (val (ff x)) (val (ff y))].

Definition hom_le g h := [exists ff, @fin_hom g h ff].

Definition hom_lt : rel (fsgraph T) :=
  fun g h => (h != g) && (hom_le g h).

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

Context (g h : fsgraph T).
Implicit Types (ff : {ffun (fld g) -> (fld h)}).

Definition fin_hom_of f homf : {ffun (fld g) -> (fld h)} := 
  [ffun x => Sub (f (val x)) (hom_fld homf (valP x))].

Definition of_fin_hom ff : T -> T := 
  fun x => odflt \i0 (omap (val \o ff) (insub x)).

Lemma fin_hom_ofE f homf x : 
  let ff := @fin_hom_of f homf in
  f (val x) = val (ff x).
Proof. by rewrite /fin_hom_of /= ffunE. Qed.

Lemma of_fin_homE ff x : 
  let f := @of_fin_hom ff in
  f (val x) = val (ff x).
Proof. by rewrite /of_fin_hom /= insubT // => ?; rewrite sub_val. Qed.

Lemma fin_hom_ofK f homf x : 
  x \in fld g -> of_fin_hom (@fin_hom_of f homf) x = f x.
Proof. 
  move=> xin; have->: x = val (Sub x xin : fld g) by done.  
  by rewrite of_fin_homE fin_hom_ofE.
Qed.

Context (f : T -> T) (ff : {ffun (fld g) -> (fld h)}).
Hypothesis (feq : forall x, f (val x) = val (ff x)).

Lemma fin_homP : 
  reflect (hom f g h) (@fin_hom g h ff).
Proof. 
  apply/(equivP (homo2P _ _ _))=> /=; split; last first.
  - move=> homf x y; rewrite -!feq; exact/homf.
  move=> homf x y /[dup] /fld_restr /= /andP[xin yin]. 
  have->: x = val (Sub x xin : fld g) by done. 
  have->: y = val (Sub y yin : fld g) by done. 
  by move=> /homf; rewrite !feq. 
Qed.

End Def.

Arguments fin_hom {T} g h.

Section Theory.
Context {T : identType}.
Implicit Types (f : T -> T) (g h : fsgraph T).

Lemma hom_mapP f g h : 
  reflect (hom f g h) (f @` g `<=` h).
Proof. 
  apply/equivP; first exact/fsubsetP; split. 
  - by move=> subs x y ?; apply/subs/imfsetP; exists (x, y).
  move=> homf [??] /imfsetP[[??]] /= + [-> ->]. 
  by rewrite -!fsgraphE=> /homf.
Qed.

Lemma hom_leP g h :
  reflect (exists f, hom f g h) (hom_le g h).
Proof.
  apply/(equivP (existsPP _)). 
  - by move=> /= ff; apply/fin_homP/of_fin_homE. 
  move=> /=; split=> [[ff] ? | [f]].
  - by exists (of_fin_hom ff).
  move=> homf; exists (fin_hom_of homf).
  move=> x y /[dup] /fld_restr /andP[??]. 
  rewrite !fin_hom_ofK //; exact/homf.
Qed. 

Lemma hom_lt_def g h : 
  hom_lt g h = (h != g) && (hom_le g h).
Proof. done. Qed.

Lemma hom_le_refl : 
  reflexive (@hom_le T).
Proof. by move=> g; apply/hom_leP; exists id. Qed.

Lemma hom_le_trans : 
  transitive (@hom_le T).
Proof. 
  move=> ??? /hom_leP[f] homf /hom_leP[g] homg. 
  apply/hom_leP; exists (g \o f)=> ??? /=. 
  exact/homg/homf.
Qed.

Lemma hom_le_emp g : hom_le [emp] g.
Proof. by apply/hom_leP; exists id. Qed.

End Theory.

End Hom.


Module Export iHom.
Section Def. 
Context {T : identType}.
Implicit Types (f : T -> T) (g h : fsgraph T).

Definition ihom f g h := 
  [/\ {homo f : x y / g x y >-> h x y}
    & {in (fld g) &, injective f}
  ].

Definition fin_ihom g h (ff : {ffun (fld g) -> (fld h)}) := 
  fin_hom g h ff && injectiveb ff.

Definition ihom_le g h := [exists ff, @fin_ihom g h ff].

Definition ihom_lt : rel (fsgraph T) :=
  fun g h => (h != g) && (ihom_le g h).

Context (g h : fsgraph T).
Context (f : T -> T) (ff : {ffun (fld g) -> (fld h)}).
Hypothesis (feq : forall x : fld g, f (val x) = val (ff x)).

Lemma fin_ihomP : 
  reflect (ihom f g h) (@fin_ihom g h ff).
Proof. 
  apply/(equivP (andPP (fin_homP _) _)) => //; last exact: iff_refl.
  apply/(equivP (injectiveP _)); split=> injf /= x y; last first.
  - move=> H; apply/val_inj/injf; try exact/valP.
    by rewrite !feq H.
  move=> xin yin.
  have->: x = val (Sub x xin : fld g) by done.
  have->: y = val (Sub y yin : fld g) by done.
  by rewrite !feq=> /val_inj/injf ->.
Qed.

End Def.

Arguments fin_ihom {T} g h.

Section Theory.
Context {T : identType}.
Implicit Types (f : T -> T) (g h : fsgraph T).

(* Lemma ihom_mapP f g h :  *)
(*   reflect (hom f g h) (f @` g `<=` h). *)
(* Proof.  *)
(*   apply/equivP; first exact/fsubsetP; split.  *)
(*   - by move=> subs x y ?; apply/subs/imfsetP; exists (x, y). *)
(*   move=> homf [??] /imfsetP[[??]] /= + [-> ->].  *)
(*   by rewrite -!fsgraphE=> /homf. *)
(* Qed. *)

Lemma ihom_leP g h :
  reflect (exists f, ihom f g h) (ihom_le g h).
Proof.
  apply/(equivP (existsPP _)). 
  - by move=> /= ff; apply/fin_ihomP/of_fin_homE. 
  move=> /=; split=> [[ff] ? | [f]].
  - by exists (of_fin_hom ff).
  move=> [homf injf]; exists (fin_hom_of homf); split. 
  - move=> x y /[dup] /fld_restr /andP[??]. 
    rewrite !fin_hom_ofK //; exact/homf.
  move=> x y ??; rewrite !fin_hom_ofK //; exact/injf.
Qed. 

Lemma ihom_lt_def g h : 
  ihom_lt g h = (h != g) && (ihom_le g h).
Proof. done. Qed.

Lemma ihom_le_refl : 
  reflexive (@ihom_le T).
Proof. by move=> g; apply/ihom_leP; exists id; split. Qed.

Lemma hom_le_trans : 
  transitive (@ihom_le T).
Proof. 
  move=> ??? /ihom_leP[f] [homf injf] /ihom_leP[g] [homg injg]. 
  apply/ihom_leP; exists (g \o f); split; move=> /= *. 
  - exact/homg/homf.
  apply/injf/injg=> //; exact/(hom_fld homf).
Qed.

Lemma ihom_le_emp g : ihom_le [emp] g.
Proof. by apply/ihom_leP; exists id; split. Qed.

End Theory.

End iHom.

Section KleeneAlgebra.
Context {T U : identType}.

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

