From Coq Require Import Relations Relation_Operators.
From RelationAlgebra Require Import lattice monoid rel kat_tac.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat zify. 
From mathcomp Require Import eqtype choice seq order path.
From mathcomp Require Import fintype finfun fingraph finmap.
From mathcomp.tarjan Require Import extra acyclic kosaraju acyclic_tsorted. 
From eventstruct Require Import utils seq rel_algebra rel fsrel inhtype ident.

(******************************************************************************)
(* A theory of finitely supported graphs.                                     *)
(* TODO.                                                                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset_scope.
Local Open Scope ident_scope.
Local Open Scope rel_scope.
Local Open Scope fsrel_scope.

Declare Scope fsgraph_scope.
Delimit Scope fsgraph_scope with fsgraph.

Local Open Scope fsgraph_scope.

Module FsGraph.

Module Export Def.
Section Def.
Context (T : identType) (L : botType).

Record fsgraph := mk_fsgraph {
  lab   : {fsfun T -> L with bot};
  edges : fsrel T;
}.

Implicit Types (g : fsgraph).

Definition nodes g := finsupp (lab g).

Coercion rel_of_fsgraph g : rel T := 
  fun x y => (x, y) \in edges g.

Definition fsgraph_apply g : T -> T -> bool := rel_of_fsgraph g.
Coercion fsgraph_apply : fsgraph >-> Funclass.

Definition fsgraph0 : fsgraph := 
  mk_fsgraph [fsfun] fset0.

Definition prod_of_fsgraph g := (lab g, edges g).
Definition fsgraph_of_prod := fun '(f, es) => mk_fsgraph f es.

Lemma prod_of_fsgraph_inj : injective prod_of_fsgraph.
Proof. by move=> [??] [??] [-> ->]. Qed.

Lemma prod_of_fsgraphK : cancel prod_of_fsgraph fsgraph_of_prod.
Proof. by case. Qed.

Definition fsgraph_eqMixin := InjEqMixin (prod_of_fsgraph_inj). 
Canonical fsgraph_eqType := 
  Eval hnf in EqType fsgraph fsgraph_eqMixin.

Definition fsgraph_choiceMixin := CanChoiceMixin prod_of_fsgraphK.
Canonical fsgraph_choiceType := 
  Eval hnf in ChoiceType fsgraph fsgraph_choiceMixin.

End Def.
End Def.

Arguments fsgraph0 {T L}.

Module Export Syntax. 
Notation "[ 'emp' ]" := (fsgraph0)
  (at level 0, format "[ 'emp' ]") : fsgraph_scope.
End Syntax.


Module Export Theory.
Section Theory.
Context {T U : identType} {L : botType}.
Implicit Types (g h : fsgraph T L).
Implicit Types (f : T -> T).

Lemma fsgraphE g x y : (g x y) = ((x, y) \in edges g).
Proof. done. Qed.

Lemma mem_nodes g x : 
  (x \in nodes g) = (lab g x != bot).
Proof. by rewrite mem_finsupp. Qed.

Lemma memNnodes g x : 
  (x \notin nodes g) = (lab g x == bot).
Proof. by rewrite memNfinsupp. Qed.

Lemma lab_bot g x :
  (x \notin nodes g) -> lab g x = bot.
Proof. by rewrite memNnodes=> /eqP. Qed.

Lemma nodes_emp : 
  nodes ([emp] : fsgraph T L) = fset0.
Proof. by rewrite /nodes finsupp0. Qed.

End Theory.
End Theory.


Module Export Hom.
Module Export Def.
Section Def. 
Context {T : identType} {L : botType}.
Implicit Types (g h : fsgraph T L).
Implicit Types (f : T -> T).

Definition lab_mono f g h := 
  {mono f : x / lab g x >-> lab h x}.  

Definition edge_homo f g h :=
  {in (nodes g) &, {homo f : x y / g x y >-> h x y}}.

Definition hom f g h := 
  [/\ lab_mono f g h & edge_homo f g h].

Context (g h : fsgraph T L).
Implicit Types (ff : {ffun (nodes g) -> (nodes h)}).

Definition fin_lab_mono ff := 
  [forall x, lab h (val (ff x)) == lab g (val x)].

Definition fin_edge_homo ff := 
  [forall x, forall y, (g (val x) (val y)) ==> h (val (ff x)) (val (ff y))].

Definition fin_hom ff := 
  [&& fin_lab_mono ff & fin_edge_homo ff].

Definition hom_le := [exists ff, fin_hom ff].
Definition hom_lt := (h != g) && hom_le.

Lemma lab_mono_mem_nodes f x : 
  lab_mono f g h -> (x \in nodes g) = (f x \in nodes h).
Proof. by rewrite !mem_nodes => ->. Qed.

Lemma lab_mono_nodes f x : 
  lab_mono f g h -> x \in nodes g -> f x \in nodes h.
Proof. by rewrite !mem_nodes => ->. Qed.

Definition fin_hom_of f labf : {ffun (nodes g) -> (nodes h)} := 
  [ffun x => Sub (f (val x)) (lab_mono_nodes labf (valP x))].

Definition of_fin_hom ff : T -> T := 
  fun x => odflt (fresh_seq (nodes h)) (omap (val \o ff) (insub x)).

End Def.
End Def.

Arguments fin_lab_mono {T L} g h.
Arguments fin_edge_homo {T L} g h.
Arguments fin_hom {T L} g h.
Arguments fin_hom_of {T L} g h f.

Module Export Theory.
Section Theory.
Context {T : identType} {L : botType}.
Implicit Types (g h : fsgraph T L).
Implicit Types (f : T -> T).

Section FinHom.
Context (g h : fsgraph T L).
Context (f : T -> T) (ff : {ffun (nodes g) -> (nodes h)}).
Hypothesis (Heq : forall x, f (val x) = val (ff x)).
Hypothesis (Hnodes : forall x, x \notin nodes g -> f x \notin nodes h).

Lemma lab_monoW :
  lab_mono f g h -> fin_lab_mono g h ff.
Proof. by move=> /= labf; apply/mono1P=> x; rewrite -labf Heq. Qed.

Lemma fin_lab_monoS :
  fin_lab_mono g h ff -> lab_mono f g h.
Proof. 
  move=> /= /mono1P labf x.
  case: (x \in nodes g)/idP=> [xin|]; last first.
  - by move=> /negP /[dup] /Hnodes ??; rewrite !lab_bot.
  have->: x = val (Sub x xin : nodes g)=> //.
  by rewrite Heq labf.
Qed.

Lemma edge_homoP : 
  reflect (edge_homo f g h) (fin_edge_homo g h ff).
Proof. 
  apply/(equivP (homo2P _ _ _))=> /=; split; last first.
  - move=> homf x y; rewrite -!Heq; exact/homf.
  move=> homf x y xin yin. 
  have->: x = val (Sub x xin : nodes g) by done. 
  have->: y = val (Sub y yin : nodes g) by done. 
  by move=> /homf; rewrite !Heq. 
Qed.

Lemma fin_homP : 
  reflect (hom f g h) (fin_hom g h ff).
Proof. 
  apply/andPP; last exact/edge_homoP.
  apply/(equivP idP); split; [exact/fin_lab_monoS | exact/lab_monoW].
Qed.

End FinHom.

Lemma lab_mono_comp f f' g h j : 
  lab_mono f g h -> lab_mono f' h j -> lab_mono (f' \o f) g j.
Proof. by move=> labf labf' x /=; rewrite labf' labf. Qed.

Lemma edge_homo_comp f f' g h j : lab_mono f g h ->
  edge_homo f g h -> edge_homo f' h j -> edge_homo (f' \o f) g j.
Proof. 
  move=> labf homf homf' x y ??? /=. 
  by apply/homf'/homf=> //; apply/lab_mono_nodes. 
Qed.

Lemma fin_hom_ofE g h f labf x : 
  let ff := fin_hom_of g h f labf in
  f (val x) = val (ff x).
Proof. by rewrite /fin_hom_of /= ffunE. Qed.

Lemma of_fin_homE g h (ff : {ffun (nodes g) -> (nodes h)}) x : 
  let f := of_fin_hom ff in
  f (val x) = val (ff x).
Proof. by rewrite /of_fin_hom /= insubT // => ?; rewrite sub_val. Qed.

Lemma of_fin_hom_nodes g h (ff : {ffun (nodes g) -> (nodes h)}) x :
  let f := of_fin_hom ff in
  x \notin nodes g -> f x \notin nodes h.
Proof. 
  move=> f xnin; rewrite /f /of_fin_hom insubF /=; last exact: negPf.
  exact/fresh_seq_nmem. 
Qed.
  
Lemma fin_hom_ofK g h f labf x : 
  x \in nodes g -> of_fin_hom (fin_hom_of g h f labf) x = f x.
Proof. 
  move=> xin; have->: x = val (Sub x xin : nodes g) by done.  
  by rewrite of_fin_homE (fin_hom_ofE labf).
Qed.

Lemma hom_leP g h :
  reflect (exists f, hom f g h) (hom_le g h).
Proof.
  apply/(equivP (existsPP _)). 
  - move=> /= ff; apply/fin_homP; first exact/of_fin_homE.
    exact/of_fin_hom_nodes.
  move=> /=; split=> [[ff] ? | [f]].
  - by exists (of_fin_hom ff).
  move=> [labf homf]; exists (fin_hom_of g h f labf); split; last first.
  - move=> x y xin yin; rewrite !fin_hom_ofK //; exact/homf.
  move=> x; case: (x \in nodes g)/idP=> [xin|].
  - rewrite fin_hom_ofK //; exact/labf.
  move=> /negP xnin; rewrite /of_fin_hom insubF /=; last exact: negPf. 
  rewrite !lab_bot //; exact/fresh_seq_nmem.
Qed.

Lemma hom_lt_def g h : 
  hom_lt g h = (h != g) && (hom_le g h).
Proof. done. Qed.

Lemma hom_le_refl : 
  reflexive (@hom_le T L).
Proof. by move=> g; apply/hom_leP; exists id; split. Qed.

Lemma hom_le_trans : 
  transitive (@hom_le T L).
Proof. 
  move=> ??? /hom_leP[f] [labf homf] /hom_leP[g] [labg homg]. 
  apply/hom_leP; exists (g \o f). 
  split; [exact/lab_mono_comp | exact/edge_homo_comp]. 
Qed.

Lemma hom_le_emp g : hom_le [emp] g.
Proof. 
  apply/hom_leP; exists (fun x => fresh_seq (nodes g)). 
  split=> // x; rewrite !lab_bot ?nodes_emp ?inE //. 
  exact/fresh_seq_nmem.
Qed.

End Theory.
End Theory.

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

Module Export Syntax. 
Notation "g \subgraph h" := (ihom_le g h)
  (at level 70, format "g  \subgraph  h") : fsgraph_scope.
End Syntax.

Section Theory.
Context {T : identType}.
Implicit Types (f : T -> T) (g h : fsgraph T).

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

Lemma ihom_le_size g h : 
  ihom_le g h -> (#|`fld g| <= #|`fld h|)%N.
Proof. by rewrite !cardfE=> /existsP /= [f] /andP[_ /injectiveP] /leq_card. Qed.
  
Lemma ihom_lt_def g h : 
  ihom_lt g h = (h != g) && (ihom_le g h).
Proof. done. Qed.

Lemma ihom_le_refl : 
  reflexive (@ihom_le T).
Proof. by move=> g; apply/ihom_leP; exists id; split. Qed.

Lemma ihom_le_trans : 
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

