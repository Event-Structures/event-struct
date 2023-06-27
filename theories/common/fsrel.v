From Coq Require Import Relations Relation_Operators.
From RelationAlgebra Require Import lattice monoid rel kat_tac.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat zify. 
From mathcomp Require Import eqtype choice seq order path.
From mathcomp Require Import fintype finfun fingraph finmap.
From mathcomp.tarjan Require Import extra acyclic kosaraju acyclic_tsorted. 
From eventstruct Require Import utils seq rel_algebra rel inhtype ident.

(******************************************************************************)
(* A theory of finitely supported relations.                                  *)
(* TODO.                                                                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope rel_scope.
Local Open Scope fset_scope.
Local Open Scope ident_scope.

Declare Scope fsrel_scope.
Delimit Scope fsrel_scope with fsrel.

Local Open Scope fsrel_scope.

Module FsRel.

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
Definition fshrel := {fset T * U}.

Implicit Types (r : fshrel).

Coercion hrel_of_fshrel r : {hrel T & U} := 
  fun x y => (x, y) \in r.

Definition fshrel_apply r : T -> U -> bool := hrel_of_fshrel r.
Coercion fshrel_apply : fshrel >-> Funclass.

Definition dom r : {fset T} := [fset (fst p) | p in r].
Definition cod r : {fset U} := [fset (snd p) | p in r].

End hDef.

Arguments fshrel T U : clear implicits.

Notation fsrel T := (fshrel T T).

Definition fsrel0 {T U} : fshrel T U := fset0.

Section Def.
Context {T U : identType}.
Implicit Types (g : fsrel T).
Implicit Types (f : T -> U).

Definition fld g : {fset T} := dom g `|` cod g.

Definition fsrel_map f g : fsrel U := 
  (fun '(x, y) => (f x, f y)) @` g.

Definition fsrel_irreflexive g : bool := 
  [forall x : fld g, ~~ (g (val x) (val x))].

Definition fsrel_transitive g : bool := 
  [forall y : fld g, forall x : fld g, forall z : fld g, 
      (g (val x) (val y)) && (g (val y) (val z)) ==> (g (val x) (val z))
  ].

End Def.
End Def.

Module Export Syntax. 
Notation "f @` r" := (fsrel_map f r)
  (at level 24) : fsrel_scope.
Notation "@! f" := (fun r => f @` r)%fsrel
  (at level 10, f at level 8, no associativity, format "@!  f") : fsrel_scope.
Notation "[ 'fsrel' E | x , y 'in' A ]" := 
  [fset p in A `*` A | (let '(x, y) := p in E)]
  (at level 0, E, x at level 99, y at level 99,
   format "[ '[hv' 'fsrel'  E '/ '  |  x , y  'in'  A ] ']'").
End Syntax.

Module Export Theory.
Section hTheory.
Context {T U : identType}.
Implicit Types (r : fshrel T U).

Lemma fsrelE r x y : (r x y) = ((x, y) \in r).
Proof. done. Qed.

Lemma fsrelP r1 r2 : 
  reflect (r1 =2 r2) (r1 == r2).
Proof. 
  apply/(equivP eqP); split=> [-> | Heq] //. 
  by apply/fsetP=> [[x y]]; rewrite -!fsrelE Heq.
Qed.

Lemma fssubrelP r1 r2 : 
  reflect (r1 \<= r2 :> {hrel T & U}) (r1 `<=` r2).
Proof. 
  apply/equivP; first exact/fsubsetP; split. 
  - by move=> subs x y /= /subs. 
  by move=> subs [??] /subs.
Qed.

Lemma domP r x : 
  reflect (exists y, r x y) (x \in dom r).
Proof. 
  apply/equivP; first by apply/imfsetP. 
  split=> [[] [y z] ? -> | [y] ?] /=; [by exists z | by exists (x, y)].
Qed.

Lemma codP r x : 
  reflect (exists y, r y x) (x \in cod r).
Proof. 
  apply/equivP; first by apply/imfsetP. 
  split=> [[] [y z] ? -> | [y] ?] /=; [by exists y | by exists (y, x)].
Qed.

Lemma dom0 : dom (fset0 : fshrel T U) = fset0. 
Proof. by apply/fsetP=> x; rewrite !inE; apply/idP=> /domP[y]. Qed.

Lemma cod0 : cod (fset0 : fshrel T U) = fset0. 
Proof. by apply/fsetP=> x; rewrite !inE; apply/idP=> /codP[y]. Qed.

Lemma dom_cod_restr r : 
  r \<= mem (dom r) \x mem (cod r) :> {hrel T & U}.
Proof. 
  move=> x y /=; rewrite /le_bool /dom /cod /=. 
  rewrite /hrel_of_fshrel=> ing. 
  by apply/andP; split; apply/imfsetP; exists (x, y).
Qed.

End hTheory.

Section Theory.
Context {T U V : identType}.
Implicit Types (r : fsrel T).
Implicit Types (f : T -> U) (g : U -> V).

Lemma fldP r x : 
  reflect (exists y, r x y \/ r y x) (x \in fld r).
Proof. 
  apply/(equivP idP); rewrite inE; split=> [/orP[] | [y []]].
  - by move=> /domP[y] ?; exists y; left.
  - by move=> /codP[y] ?; exists y; right.
  - by move=> ?; apply/orP; left; apply/domP; exists y. 
  by move=> ?; apply/orP; right; apply/codP; exists y. 
Qed.

Lemma fld_elim (P : T -> Prop) r x : 
  (forall x y, r x y -> P x /\ P y) -> x \in fld r -> P x.
Proof. by move=> H; rewrite inE=> /orP[/domP[y] | /codP[y]] /H[]. Qed.

Lemma fld0 : fld (fset0 : fsrel T) = fset0. 
Proof. by rewrite /fld dom0 cod0 fsetU0. Qed.

Lemma fld_restr r : 
  r \<= mem (fld r) \x mem (fld r) :> rel T.
Proof. 
  move=> x y /dom_cod_restr /= /andP[].
  by rewrite /fld !inE=> -> -> /=.
Qed.

Lemma fsub_fsrel D (r : rel T) : 
  fld [fsrel (r x y) | x, y in D] `<=` D.
Proof. 
  apply/fsubsetP=> x.
  pose P x := x \in D.
  apply (@fld_elim P)=> {}x y.
  move=> /imfsetP[[??]] /[swap] [[<- <-]] /=.
  by rewrite !inE /= => /andP[] /andP[].
Qed.

Lemma fsrel_map_mem f r : injective f ->
  forall x y, ((f x, f y) \in f @` r) = ((x, y) \in r).
Proof. 
  pose fp := (fun '(x, y) => (f x, f y)).
  move=> injf x y. 
  have->: (f x, f y) = fp (x, y) by done.
  rewrite /fsrel_map -/fp mem_imfset //. 
  by move=> [??] [??] [] /= /injf-> /injf->.  
Qed.

Lemma fsrel_homoP f r1 (r2 : fsrel U) : 
  reflect {homo f : x y / r1 x y >-> r2 x y} (f @` r1 `<=` r2).
Proof. 
  apply/equivP; first exact/fsubsetP; split. 
  - by move=> subs x y ?; apply/subs/imfsetP; exists (x, y).
  move=> homf [??] /imfsetP[[??]] /= + [-> ->]. 
  by rewrite -!fsrelE=> /homf.
Qed.

Lemma fsrel_irreflexiveP r : 
  reflect (irreflexive r) (fsrel_irreflexive r).
Proof. 
  apply/equivP; first apply/forallPP=> /=.
  - move=> x; exact/negPf.
  move=> /=; split=> Hirr x; [|exact/Hirr].
  apply/idP=> /[dup] /fld_restr/andP[Hx _].
  have->: (x = fsval (Sub x Hx)) by done.
  by rewrite Hirr.
Qed.

Lemma fsrel_transitiveP r : 
  reflect (transitive r) (fsrel_transitive r).
Proof. 
  apply/equivP; first apply/forall3PP=> /=.
  - move=> y x z; apply/(implyPP _ idP); exact/andP.
  split=> /= Htrans y x z; last first.
  - move=> []; exact/Htrans.
  move=> /[dup] /fld_restr/andP[Hx Hy] /[swap]. 
  move=> /[dup] /fld_restr/andP[_ Hz].
  have->: (x = fsval (Sub x Hx)) by done.
  have->: (y = fsval (Sub y Hy)) by done.
  have->: (z = fsval (Sub z Hz)) by done.
  move=> Hyz Hxy; apply/Htrans; split; [exact/Hxy | exact/Hyz]. 
Qed.

End Theory.
End Theory.

Module Export Functor.
Section Functor.
Context {T U V : identType}.
Implicit Types (r : fsrel T).
Implicit Types (f : T -> U) (g : U -> V).

Lemma fsrel_map_id r : 
  id @` r = r.
Proof. 
  apply/fsetP=> [[x y]].  
  by rewrite -(fsrel_map_mem r (@inj_id T)).
Qed.

Lemma fsrel_map_comp f g r : 
  (g \o f) @` r = (@! g \o @! f) r.
Proof.
  rewrite /fsrel_map; apply/fsetP=> /= [[x y]]. 
  apply/idP/idP=> /imfsetP /= [[{}x {}y]] + [-> ->] /=.
  - move=> ?; apply/imfsetP; exists (f x, f y)=> //. 
    by apply/imfsetP; exists (x, y).
  move=> /imfsetP /= [[{}x {}y]] /[swap] [[-> ->]] ?. 
  by apply/imfsetP; exists (x, y).
Qed.

End Functor.
End Functor.

Module Export KleeneAlgebra.
Section KleeneAlgebra.
Context {T U : identType}.
Implicit Types (r : fshrel T U).

Canonical Structure fshrel_lattice_ops : lattice.ops := {|
  lattice.car := @fshrel T U;
  lattice.leq := fsubset;
  lattice.weq := eq_op;
  lattice.cup := fsetU;
  lattice.cap := fsetI;
  lattice.neg := (fun _ => fset0);
  lattice.bot := fset0;
  lattice.top := fset0;
|}.

Lemma hrel_of_fshrel_morph : 
  lattice.morphism (CUP+CAP+BOT) hrel_of_fshrel.
Proof.
  split; try done.
  - by move=> ?? /fsubsetP subs ?? /= /subs.
  - by move=> ?? /eqP ->.
  all: by move=> ??? /= ?? /=; rewrite /hrel_of_fshrel inE. 
Qed.

Global Instance fshrel_monoid_laws: 
  lattice.laws (CUP+CAP+BOT) fshrel_lattice_ops.
Proof.
  apply/(laws_of_injective_morphism hrel_of_fshrel). 
  - exact/hrel_of_fshrel_morph.
  - by move=> r1 r2 /fssubrelP. 
  by move=> r1 r2 /fsrelP.  
Qed.

(* TODO: although fsrel does not form Kleene algebra 
 *   (because there is no common `unit` element), 
 *   we still can try to leverage kat reasoning 
 *   by lifting fshrel to hRel and applying kat there; 
 *   we should also try this idea for `rel`. 
 *)

End KleeneAlgebra.
End KleeneAlgebra.

End FsRel.

Export FsRel.Def.
Export FsRel.Theory.
Export FsRel.KleeneAlgebra.
