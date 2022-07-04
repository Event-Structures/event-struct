From Coq Require Import Relations Relation_Operators.
From RelationAlgebra Require Import lattice monoid rel kat_tac.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat zify. 
From mathcomp Require Import eqtype choice seq order path.
From mathcomp Require Import fintype finfun fingraph finmap.
From mathcomp.tarjan Require Import extra acyclic kosaraju acyclic_tsorted. 
From eventstruct Require Import utils seq rel_algebra rel fsrel. 
From eventstruct Require Import inhtype ident fperm.

(******************************************************************************)
(* A theory of finitely supported graphs.                                     *)
(* TODO.                                                                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import FsRel.Syntax. 

Local Open Scope rel_scope.
Local Open Scope fsrel_scope.
Local Open Scope fset_scope.
Local Open Scope ident_scope.

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

Definition fsg_rename (f : {fperm T}) g := 
  let flab   := [fsfun x in (f @` nodes g) => lab g (fperm_inv f x)] in 
  let fedges := (f @` (edges g))%fsrel in
  mk_fsgraph flab fedges. 

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

Definition well_restricted g := 
  (fld (edges g)) `<=` nodes g.

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
Implicit Types (f : {fperm T}).

Lemma fsgraphE g x y : (g x y) = ((x, y) \in edges g).
Proof. done. Qed.

Lemma fsgraphP g h : 
  reflect (lab g =1 lab h /\ g =2 h) (g == h).
Proof. by apply/(equivP (andPP eqP (fsrelP _ _))); rewrite fsfunP. Qed.

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

Lemma fsg_rename_labE f g : 
  lab (fsg_rename f g) =1 (lab g) \o (fperm_inv f).
Proof. 
  move=> x /=; rewrite fsfunE; case: ifP=> [|/negP/negP] //.
  rewrite -[x in x \notin _](inv_fpermK f) mem_imfset /=. 
  - by move=> nin; rewrite lab_bot.
  exact/fperm_inj.
Qed.

Lemma fsg_renameE f g : 
  (fsg_rename f g) =2 relpre (fperm_inv f) g.
Proof. 
  move=> x y; rewrite fsgraphE /=.
  rewrite -[x in (x, _)](inv_fpermK f). 
  rewrite -[y in (_, y)](inv_fpermK f). 
  rewrite fsrel_map_mem //; exact/fperm_inj.
Qed.

Lemma well_restrictedP g : 
  reflect {subset fld (edges g) <= nodes g} (well_restricted g).
Proof. exact/fsubsetP. Qed.

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

Definition lab_mono_bot f g h := 
  {in [pred x | x \notin nodes g], lab_mono f g h}.

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

Lemma lab_mono_mem_nodes f : lab_mono f g h ->
  forall x, (x \in nodes g) = (f x \in nodes h).
Proof. by move=> labf x; rewrite !mem_nodes labf. Qed.

Lemma lab_mono_nodes f x : 
  lab_mono f g h -> x \in nodes g -> f x \in nodes h.
Proof. by rewrite !mem_nodes => ->. Qed.

Definition fin_hom_of f labf : {ffun (nodes g) -> (nodes h)} := 
  [ffun x => Sub (f (val x)) (lab_mono_nodes labf (valP x))].

Definition of_fin_hom ff : T -> T := 
  fun x => odflt (fresh_seq (nodes h)) (omap (val \o ff) (insub x)).

Definition emp_hom g : T -> T := 
  fun _ => fresh_seq (nodes g).

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

Section FinHom.
Context (g h : fsgraph T L).
Context (f : T -> T) (ff : {ffun (nodes g) -> (nodes h)}).
Hypothesis (Heq : forall x, f (val x) = val (ff x)).

Lemma lab_monoP : 
  reflect {in (nodes g), lab_mono f g h} (fin_lab_mono g h ff).
Proof. 
  apply/(equivP (mono1P _ _ _))=> /=; split; last first.
  - move=> labf x; rewrite -!Heq labf //; exact/valP. 
  move=> labf x xin. 
  have->: x = val (Sub x xin : nodes g) by done. 
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

Lemma fin_homP : lab_mono_bot f g h ->
  reflect (hom f g h) (fin_hom g h ff).
Proof. 
  move=> nlabf; apply/(andPP _ edge_homoP).
  apply/(equivP lab_monoP).
  apply: iff_trans; last first.
  - apply: iff_sym; exact/(in1_split (mem (nodes g))). 
  by split=> [|[]] // labf; split. 
Qed.

End FinHom.

Section Hom.
Implicit Types (f : T -> T).

Lemma fin_hom_ofE g h f labf x : 
  let ff := fin_hom_of g h f labf in
  f (val x) = val (ff x).
Proof. by rewrite /fin_hom_of /= ffunE. Qed.

Lemma of_fin_homE g h (ff : {ffun (nodes g) -> (nodes h)}) x : 
  let f := of_fin_hom ff in
  f (val x) = val (ff x).
Proof. by rewrite /of_fin_hom /= insubT // => ?; rewrite sub_val. Qed.

Lemma of_fin_hom_bot g h (ff : {ffun (nodes g) -> (nodes h)}) :
  let f := of_fin_hom ff in
  lab_mono_bot f g h.
Proof. 
  move=> f x; rewrite inE /f /of_fin_hom=> xnin.
  rewrite insubF /=; last exact: negPf.
  rewrite !lab_bot //; exact/fresh_seq_nmem. 
Qed.
  
Lemma fin_hom_ofK g h f labf x : 
  x \in nodes g -> of_fin_hom (fin_hom_of g h f labf) x = f x.
Proof. 
  move=> xin; have->: x = val (Sub x xin : nodes g) by done.  
  by rewrite of_fin_homE (fin_hom_ofE labf).
Qed.

Lemma edge_homoS f g h : well_restricted g ->
  edge_homo f g h -> {homo f : x y / g x y >-> h x y}.
Proof. 
  move=> /well_restrictedP subs homf x y /[dup] /fld_restr /=. 
  move=> /andP[] /subs ? /subs ??; exact/homf.
Qed.

(* TODO: generalize to monomorphism? *)
Lemma lab_mono_eq f f' g h : {in (nodes g), f' =1 f} ->
  lab_mono f g h -> lab_mono_bot f' g h -> lab_mono f' g h.
Proof.
  move=> eqf labf labf'. 
  apply/in1_split; split; last exact/labf'.
  by move=> x xin; rewrite eqf.
Qed.

(* TODO: generalize to homomorphism? *)
Lemma eq_in_edge_homo f f' g h : {in (nodes g), f =1 f'} ->
  edge_homo f g h <-> edge_homo f' g h.
Proof.
  move=> eqf; split=> homf x y ??.
  - rewrite -!eqf //; exact/homf.
 rewrite !eqf //; exact/homf.
Qed.

Lemma hom_leP g h :
  reflect (exists f, hom f g h) (hom_le g h).
Proof.
  apply/(equivP (existsPP _)). 
  - move=> /= ff; apply/fin_homP; first exact/of_fin_homE.
    exact/of_fin_hom_bot.
  move=> /=; split=> [[ff] ? | [f]].
  - by exists (of_fin_hom ff).
  move=> [labf homf]; exists (fin_hom_of g h f labf); split.
  - apply/(lab_mono_eq _ labf); [exact/fin_hom_ofK | exact/of_fin_hom_bot]. 
  apply/eq_in_edge_homo; [exact/fin_hom_ofK | exact/homf].
Qed.   

Lemma emp_homP g : 
  hom (emp_hom g) [emp] g.
Proof.
  split=> // x; rewrite !lab_bot ?nodes_emp ?inE //. 
  exact/fresh_seq_nmem.
Qed.

Lemma hom_le_emp g : hom_le [emp] g.
Proof. apply/hom_leP; exists (emp_hom g); exact/emp_homP. Qed.

Lemma lab_mono_comp f f' g h j : 
  lab_mono f g h -> lab_mono f' h j -> lab_mono (f' \o f) g j.
Proof. by move=> labf labf' x /=; rewrite labf' labf. Qed.

Lemma edge_homo_comp f f' g h j : lab_mono f g h ->
  edge_homo f g h -> edge_homo f' h j -> edge_homo (f' \o f) g j.
Proof. 
  move=> labf homf homf' x y ??? /=. 
  apply/homf'/homf=> //; exact/lab_mono_nodes. 
Qed.

Lemma hom_comp f f' g h j : 
  hom f g h -> hom f' h j -> hom (f' \o f) g j.
Proof. move=> [??] [??]; split; [exact/lab_mono_comp|exact/edge_homo_comp]. Qed.

Lemma hom_lt_def g h : 
  hom_lt g h = (h != g) && (hom_le g h).
Proof. done. Qed.

Lemma hom_le_refl : 
  reflexive (@hom_le T L).
Proof. by move=> g; apply/hom_leP; exists id; split. Qed.

Lemma hom_le_trans : 
  transitive (@hom_le T L).
Proof. 
  move=> ??? /hom_leP[f] homf /hom_leP[g] ?. 
  apply/hom_leP; exists (g \o f); exact/(hom_comp homf).
Qed.

End Hom.

End Theory.
End Theory.

End Hom.


Module Export iHom.
Module Export Def.
Section Def. 
Context {T : identType} {L : botType}.
Implicit Types (g h : fsgraph T L).
Implicit Types (f : T -> T).

Definition nodes_inj f g := 
  {in (nodes g) &, injective f}.

Definition ihom f g h := 
  [/\ hom f g h & nodes_inj f g].

Context (g h : fsgraph T L).
Implicit Types (ff : {ffun (nodes g) -> (nodes h)}).

Definition fin_ihom ff := 
  [&& fin_hom g h ff & injectiveb ff].

Definition ihom_le := [exists ff, fin_ihom ff].
Definition ihom_lt := (h != g) && ihom_le.

End Def.
End Def.

Arguments fin_ihom {T L} g h.


Module Export Theory.
Section Theory.
Context {T : identType} {L : botType}.
Implicit Types (g h : fsgraph T L).
Implicit Types (f : T -> T).

Section FinIHom.
Context (g h : fsgraph T L).
Context (f : T -> T) (ff : {ffun (nodes g) -> (nodes h)}).
Hypothesis (Heq : forall x, f (val x) = val (ff x)).

Lemma nodes_injP : 
  reflect (nodes_inj f g) (injectiveb ff).
Proof. 
  apply/(equivP (injectiveP _)). split=> injf /= x y; last first.
  - move=> H; apply/val_inj/injf; try exact/valP.
    by rewrite !Heq H.
  move=> xin yin.
  have->: x = val (Sub x xin : nodes g) by done.
  have->: y = val (Sub y yin : nodes g) by done.
  by rewrite !Heq=> /val_inj/injf ->.
Qed.

Lemma fin_ihomP : lab_mono_bot f g h ->
  reflect (ihom f g h) (fin_ihom g h ff).
Proof. by move=> nlabf; apply/(andPP (fin_homP Heq nlabf) nodes_injP). Qed. 

End FinIHom.

(* TODO: generalize? *)
Lemma eq_in_nodes_inj f f' g : {in (nodes g), f =1 f'} ->
  nodes_inj f g <-> nodes_inj f' g.
Proof.
  move=> eqf; split=> injf x y ??.
  - rewrite -!eqf // => ?; exact/injf.
 rewrite !eqf // => ?; exact/injf.
Qed.

Lemma ihom_leP g h :
  reflect (exists f, ihom f g h) (ihom_le g h).
Proof.
  apply/(equivP (existsPP _)). 
  - move=> /= ff; apply/fin_ihomP; first exact/of_fin_homE.
    exact/of_fin_hom_bot.
  move=> /=; split=> [[ff] ? | [f]].
  - by exists (of_fin_hom ff).
  move=> [[labf homf] injf]; exists (fin_hom_of g h f labf); repeat split. 
  - apply/(lab_mono_eq _ labf); [exact/fin_hom_ofK | exact/of_fin_hom_bot]. 
  - apply/eq_in_edge_homo; [exact/fin_hom_ofK | exact/homf].
  apply/eq_in_nodes_inj; [exact/fin_hom_ofK | exact/injf].
Qed.

Lemma ihom_hom f g h : 
  ihom f g h -> hom f g h.
Proof. by move=> []. Qed.

Lemma ihom_hom_le g h : 
  ihom_le g h -> hom_le g h.
Proof. by move=> /ihom_leP[f] /ihom_hom ?; apply/hom_leP; exists f. Qed.

Lemma ihom_le_size g h : 
  ihom_le g h -> (#|`nodes g| <= #|`nodes h|)%N.
Proof. by rewrite !cardfE=> /existsP /= [f] /andP[_ /injectiveP] /leq_card. Qed.

Lemma emp_ihomP g : 
  ihom (emp_hom g) [emp] g.
Proof.
  split; first exact/emp_homP.
  by move=> ??; rewrite nodes_emp inE.
Qed.

Lemma ihom_le_emp g : ihom_le [emp] g.
Proof. apply/ihom_leP; exists (emp_hom g); exact/emp_ihomP. Qed.

Lemma ihom_comp f f' g h j : 
  ihom f g h -> ihom f' h j -> ihom (f' \o f) g j.
Proof. 
  move=> [/[dup] ? [labf _] injf] [? injf']; split. 
  - by apply/hom_comp; eauto. 
  move=> x y ?? /= ?; apply/injf/injf'=> //; exact/lab_mono_nodes. 
Qed.

Lemma ihom_lt_def g h : 
  ihom_lt g h = (h != g) && (ihom_le g h).
Proof. done. Qed.

Lemma ihom_le_refl : 
  reflexive (@ihom_le T L).
Proof. by move=> g; apply/ihom_leP; exists id; repeat split. Qed.

Lemma ihom_le_trans : 
  transitive (@ihom_le T L).
Proof. 
  move=> ??? /ihom_leP[f] ihomf /ihom_leP[g] ?. 
  apply/ihom_leP; exists (g \o f); exact/(ihom_comp ihomf).
Qed.

End Theory.
End Theory.

End iHom.


Module Export bHom.
Module Export Def.
Section Def. 
Context {T : identType} {L : botType}.
Implicit Types (g h : fsgraph T L).
Implicit Types (f : T -> T).

Definition nodes_bij f h :=
  {on (nodes h), bijective f}.

Definition bhom f g h := 
  [/\ hom f g h & nodes_bij f h].

Context (g h : fsgraph T L).
Implicit Types (ff : {ffun (nodes g) -> (nodes h)}).

Definition fin_bhom ff := 
  [&& fin_hom g h ff & bijectiveb ff].

Definition bhom_le := [exists ff, fin_bhom ff].
Definition bhom_lt := (h != g) && bhom_le.

End Def.
End Def.

Arguments fin_bhom {T L} g h.

Module Export Theory.
Section Theory.
Context {T : identType} {L : botType}.
Implicit Types (g h : fsgraph T L).

Section FinBHom.
Context (g h : fsgraph T L).
Context (f : T -> T) (ff : {ffun (nodes g) -> (nodes h)}).
Hypothesis (Heq : forall x, f (val x) = val (ff x)).

Lemma nodes_bijP : lab_mono f g h ->
  reflect (nodes_bij f h) (bijectiveb ff).
Proof.
  move=> labf; apply/(equivP (bijectiveP _)); split.
  - move=> [] ff' K K'.
    pose f' := of_fin_hom [ffun x => ff' x].
    have Heq': forall x, f' (val x) = val (ff' x).
    + move=> /= x; rewrite /f' /of_fin_hom insubT //= => xin. 
      by rewrite ffunE sub_val.
    exists f'=> [x | x xin]; last first.
    + have->: x = val (Sub x xin : nodes h) by done.
      by rewrite Heq' Heq K'.
    move=> /[dup] fxin. 
    rewrite -(lab_mono_mem_nodes labf) => xin. 
    have->: x = val (Sub x xin : nodes g) by done.
    by rewrite Heq Heq' K.
  case=> f' K K'.
  have suppf' : forall x, x \in nodes h -> (f' x) \in nodes g.
  - move=> x /[dup] xin; rewrite !mem_nodes. 
    by rewrite -[x in lab h x]K' // labf. 
  pose ff' : (nodes h) -> (nodes g) := 
    fun x => Sub (f' (val x)) (suppf' (val x) (valP x)). 
  exists ff'=> x; rewrite /ff'; apply/val_inj => /=. 
  - rewrite -Heq K // -(lab_mono_mem_nodes labf); exact/valP.
  by rewrite -Heq K' //. 
Qed.

Lemma fin_bhomP : lab_mono_bot f g h ->
  reflect (bhom f g h) (fin_bhom g h ff).
Proof. 
  move=> nlabf; apply/(equivP idP); split.
  - move=> /andP[] /(fin_homP Heq nlabf) homf bijf; split=> //.
    by apply/nodes_bijP=> //; case: homf.
  move=> [homf bijf]; apply/andP; split; first exact/fin_homP.
  by apply/nodes_bijP=> //; case: homf.
Qed.

End FinBHom.

Section BHom.
Implicit Types (f : T -> T).

(* TODO: generalize? *)
Lemma eq_in_nodes_bij f f' g h : lab_mono f g h -> lab_mono f' g h -> 
  {in (nodes g), f =1 f'} -> nodes_bij f h <-> nodes_bij f' h.
Proof.
  move=> labf labf' eqf; split=> [] [ff] K K'; exists ff=> x. 
  - move=> /[dup] fxin.
    rewrite -(lab_mono_mem_nodes labf')=> xin.
    by rewrite -eqf ?K -?(lab_mono_mem_nodes labf). 
  - move=> xin; rewrite -eqf ?K' //.
    by rewrite (lab_mono_mem_nodes labf) K'. 
  - move=> /[dup] fxin.
    rewrite -(lab_mono_mem_nodes labf)=> xin.
    by rewrite eqf ?K // -eqf.
  move=> xin; rewrite eqf ?K' //.
  by rewrite (lab_mono_mem_nodes labf') K'. 
Qed.

Lemma bhom_leP g h :
  reflect (exists f, bhom f g h) (bhom_le g h).
Proof.
  apply/(equivP (existsPP _)). 
  - move=> /= ff; apply/fin_bhomP; first exact/of_fin_homE.
    exact/of_fin_hom_bot.
  move=> /=; split=> [[ff] ? | [f]].
  - by exists (of_fin_hom ff).
  move=> [[labf homf] bijf]; exists (fin_hom_of g h f labf); repeat split. 
  - apply/(lab_mono_eq _ labf); [exact/fin_hom_ofK | exact/of_fin_hom_bot]. 
  - apply/eq_in_edge_homo; [exact/fin_hom_ofK | exact/homf].
  apply/(eq_in_nodes_bij _ labf)=> //; last exact/fin_hom_ofK.  
  apply/(lab_mono_eq _ labf); [exact/fin_hom_ofK | exact/of_fin_hom_bot]. 
Qed.

Lemma bhom_hom f g h : 
  bhom f g h -> hom f g h.
Proof. by move=> []. Qed.

Lemma bhom_ihom f g h : 
  bhom f g h -> ihom f g h.
Proof. 
  move=> [] /[dup] homf [labf _].
  pose ff := fin_hom_of g h f labf.
  move=> /(nodes_bijP (fin_hom_ofE labf) labf) /bijectiveP bijff. 
  split; first exact/homf.
  exact/(nodes_injP (fin_hom_ofE labf))/injectiveP/bij_inj.
Qed.

Lemma bhom_hom_le g h : 
  bhom_le g h -> hom_le g h.
Proof. by move=> /bhom_leP[f] /bhom_hom ?; apply/hom_leP; exists f. Qed.

Lemma bhom_ihom_le g h : 
  bhom_le g h -> ihom_le g h.
Proof. by move=> /bhom_leP[f] /bhom_ihom ?; apply/ihom_leP; exists f. Qed.

Lemma bhom_le_size g h : 
  bhom_le g h -> (#|`nodes g| <= #|`nodes h|)%N.
Proof. by move=> /bhom_ihom_le /ihom_le_size. Qed.

Lemma bhom_comp fg fh g h j : 
  bhom fg g h -> bhom fh h j -> bhom (fh \o fg) g j.
Proof. 
  move=> [] /[dup] [[labfg _]] homfg bijfg. 
  move=> [] /[dup] [[labfh _]] homfh bijfh. 
  split; first exact/(hom_comp homfg homfh). 
  case: bijfg=> fg' Kg Kg'; case: bijfh=> fh' Kh Kh'.  
  exists (fg' \o fh')=> x /= xin.
  - by rewrite Kh ?Kg ?(lab_mono_mem_nodes labfh). 
  by rewrite Kg' ?Kh' ?(lab_mono_mem_nodes labfh) ?Kh'. 
Qed.

Lemma bhom_lt_def g h : 
  bhom_lt g h = (h != g) && (bhom_le g h).
Proof. done. Qed.

Lemma bhom_le_refl : 
  reflexive (@bhom_le T L).
Proof. by move=> g; apply/bhom_leP; exists id; repeat split=> //; exists id. Qed.

Lemma bhom_le_trans : 
  transitive (@bhom_le T L).
Proof. 
  move=> ??? /bhom_leP[f] bhomf /bhom_leP[g] ?. 
  apply/bhom_leP; exists (g \o f); exact/(bhom_comp bhomf).
Qed.

End BHom.

Section FPermBHom.
Implicit Types (f : {fperm T}).

Lemma perm_bhom f g h :
  hom f g h -> bhom f g h.
Proof. move=> homf; split=> //; exact/onW_bij/fperm_bij. Qed.

End FPermBHom.

End Theory.
End Theory.

End bHom.


Module Export Emb.
Module Export Def.
Section Def. 
Context {T : identType} {L : botType}.
Implicit Types (g h : fsgraph T L).
Implicit Types (f : T -> T).

Definition edge_mono f g h :=
  {in (nodes g) &, {mono f : x y / g x y >-> h x y}}.

(* TODO: the term embedding is borrowed from `partial order` embedding. 
 *   In the context of graph theory it can means something else. 
 *   Need to recheck literature, maybe there is conventional name for this. 
 *)
Definition emb f g h := 
  [/\ lab_mono f g h & edge_mono f g h].

Context (g h : fsgraph T L).
Implicit Types (ff : {ffun (nodes g) -> (nodes h)}).

Definition fin_edge_mono ff := 
  [forall x, forall y, h (val (ff x)) (val (ff y)) == (g (val x) (val y))].

Definition fin_emb ff := 
  [&& fin_lab_mono g h ff & fin_edge_mono ff].

Definition emb_le := [exists ff, fin_emb ff].
Definition emb_lt := (h != g) && emb_le.

End Def.
End Def.

Arguments fin_edge_mono {T L} g h.
Arguments fin_emb {T L} g h.


Module Export Theory.
Section Theory.
Context {T : identType} {L : botType}.
Implicit Types (g h : fsgraph T L).

Section FinEmb.
Context (g h : fsgraph T L).
Context (f : T -> T) (ff : {ffun (nodes g) -> (nodes h)}).
Hypothesis (Heq : forall x, f (val x) = val (ff x)).

Lemma edge_monoP : 
  reflect (edge_mono f g h) (fin_edge_mono g h ff).
Proof. 
  apply/(equivP (mono2P _ _ _))=> /=; split; last first.
  - move=> monf x y; rewrite -!Heq monf //; exact/valP.
  move=> monf x y xin yin. 
  have->: x = val (Sub x xin : nodes g) by done. 
  have->: y = val (Sub y yin : nodes g) by done. 
  by rewrite !Heq monf. 
Qed.

Lemma fin_embP : lab_mono_bot f g h ->
  reflect (emb f g h) (fin_emb g h ff).
Proof. 
  move=> nlabf; apply/(andPP _ edge_monoP). 
  apply/(equivP (lab_monoP Heq)).
  apply: iff_trans; last first.
  - apply: iff_sym; exact/(in1_split (mem (nodes g))). 
  by split=> [|[]] // labf; split. 
Qed.

End FinEmb.

Section Emb.
Implicit Types (f : T -> T).

Lemma edge_monoW f g h : 
  edge_mono f g h -> edge_homo f g h. 
Proof. by move=> monof x y ??; rewrite monof. Qed.

Lemma edge_monoS f g h : well_restricted g -> well_restricted h ->
  lab_mono f g h -> edge_mono f g h -> {mono f : x y / g x y >-> h x y}.
Proof. 
  move=> wrg /well_restrictedP subs labf monof x y. 
  apply/idP/idP; last first.
  - exact/(edge_homoS wrg)/edge_monoW.
  move=> /[dup] /fld_restr /= /andP[] /subs + /subs. 
  rewrite -!(lab_mono_mem_nodes labf)=> ??. 
  by rewrite monof.
Qed.

(* TODO: generalize *)
Lemma eq_in_edge_mono f f' g h : {in (nodes g), f =1 f'} ->
  edge_mono f g h <-> edge_mono f' g h.
Proof.
  move=> eqf; split=> monf x y ??.
  - rewrite -!eqf //; exact/monf.
 rewrite !eqf //; exact/monf.
Qed.

Lemma emb_leP g h :
  reflect (exists f, emb f g h) (emb_le g h).
Proof.
  apply/(equivP (existsPP _)). 
  - move=> /= ff; apply/fin_embP; first exact/of_fin_homE.
    exact/of_fin_hom_bot.
  move=> /=; split=> [[ff] ? | [f]].
  - by exists (of_fin_hom ff).
  move=> [labf homf]; exists (fin_hom_of g h f labf); split; last first.
  - apply/eq_in_edge_mono; [exact/fin_hom_ofK | exact/homf].
  apply/(lab_mono_eq _ labf); [exact/fin_hom_ofK | exact/of_fin_hom_bot]. 
Qed. 

Lemma emb_hom f g h : 
  emb f g h -> hom f g h.
Proof. by move=> [] ? /monoW_in ?; split. Qed.

Lemma emb_ihom f g h : reflexive h -> antisymmetric g ->
  emb f g h -> ihom f g h.
Proof. 
  move=> refl asym embf. 
  split; first exact/emb_hom.
  exact/(mono_inj_in refl asym)/(snd embf).
Qed.

Lemma emb_hom_le g h : 
  emb_le g h -> hom_le g h.
Proof. by move=> /emb_leP[f] /emb_hom ?; apply/hom_leP; exists f. Qed.

Lemma emb_ihom_le g h : reflexive h -> antisymmetric g ->
  emb_le g h -> ihom_le g h.
Proof. 
  move=> refl asym /emb_leP[f] /(emb_ihom refl asym) ?. 
  by apply/ihom_leP; exists f. 
Qed.

Lemma emp_embP g : 
  emb (emp_hom g) [emp] g.
Proof.
  repeat split=> // x; rewrite ?lab_bot ?nodes_emp ?inE //. 
  exact/fresh_seq_nmem.
Qed.

Lemma emb_le_emp g : emb_le [emp] g.
Proof. apply/emb_leP; exists (emp_hom g); exact/emp_embP. Qed.

Lemma edge_mono_comp f f' g h j : lab_mono f g h ->
  edge_mono f g h -> edge_mono f' h j -> edge_mono (f' \o f) g j.
Proof. 
  move=> labf monf monf' x y ?? /=. 
  by rewrite monf' ?monf // -(lab_mono_mem_nodes labf).
Qed.

Lemma emb_comp f f' g h j : 
  emb f g h -> emb f' h j -> emb (f' \o f) g j.
Proof. move=> [??] [??]; split; [exact/lab_mono_comp|exact/edge_mono_comp]. Qed.

Lemma emb_lt_def g h : 
  emb_lt g h = (h != g) && (emb_le g h).
Proof. done. Qed.

Lemma emb_le_refl : 
  reflexive (@emb_le T L).
Proof. by move=> g; apply/emb_leP; exists id; split. Qed.

Lemma emb_le_trans : 
  transitive (@emb_le T L).
Proof. 
  move=> ??? /emb_leP[f] embf /emb_leP[g] ?. 
  apply/emb_leP; exists (g \o f); exact/(emb_comp embf).
Qed.

End Emb.

Section FPermEmb. 
Implicit Types (f : {fperm T}).

Lemma fsg_rename_emb f g : 
  emb f g (fsg_rename f g).
Proof. 
  split=> [x |x y xin yin].
  - by rewrite fsg_rename_labE /= fperm_invK.
  by rewrite fsg_renameE /= !fperm_invK.
Qed.

End FPermEmb.

End Theory.
End Theory.

End Emb.


Module Export Iso.
Module Export Def.
Section Def. 
Context {T : identType} {L : botType}.
Implicit Types (g h : fsgraph T L).
Implicit Types (f : T -> T).

Definition iso f g h := 
  [/\ lab_mono f g h, edge_mono f g h & nodes_bij f h].

Context (g h : fsgraph T L).
Implicit Types (ff : {ffun (nodes g) -> (nodes h)}).

Definition fin_iso ff := 
  [&& fin_lab_mono g h ff, fin_edge_mono g h ff & bijectiveb ff].

Definition iso_eqv := [exists ff, fin_iso ff].

End Def.
End Def.

Arguments fin_iso {T L} g h.


Module Export Theory.
Section Theory.
Context {T : identType} {L : botType}.
Implicit Types (g h : fsgraph T L).

Section FinIso.
Context (g h : fsgraph T L).
Context (f : T -> T) (ff : {ffun (nodes g) -> (nodes h)}).
Hypothesis (Heq : forall x, f (val x) = val (ff x)).

Lemma isoE : iso f g h <-> bhom f g h /\ emb f g h. 
Proof. split=> [[]|[[??] []]] *; repeat split=> //; exact/monoW_in. Qed.

Lemma fin_isoP : lab_mono_bot f g h ->
  reflect (iso f g h) (fin_iso g h ff).
Proof. 
  move=> nlabf; apply/(equivP _); last first.
  - apply: iff_sym; exact/isoE.
  apply/(equivP idP); split=> [|[]]; last first.
  - move=> [[labf _]] /(nodes_bijP Heq labf). 
    move=>  ? /(fin_embP Heq nlabf) /andP[??].
    exact/and3P.
  move=> /and3P[] /(lab_monoP Heq) ilabf. 
  have labf: lab_mono f g h.    
  - apply/in1_split; split; [exact/ilabf | exact/nlabf]. 
  move=> /(edge_monoP Heq) monf /(nodes_bijP Heq labf) bijf.  
  repeat split=> //; exact/monoW_in. 
Qed.

End FinIso.

Section Iso.
Implicit Types (f : T -> T).

Lemma iso_eqvP g h :
  reflect (exists f, iso f g h) (iso_eqv g h).
Proof.
  apply/(equivP (existsPP _)). 
  - move=> /= ff; apply/fin_isoP; first exact/of_fin_homE.
    exact/of_fin_hom_bot.
  move=> /=; split=> [[ff] ? | [f]].
  - by exists (of_fin_hom ff).
  move=> [labf homf]; exists (fin_hom_of g h f labf); split.
  - apply/(lab_mono_eq _ labf); [exact/fin_hom_ofK | exact/of_fin_hom_bot]. 
  - apply/eq_in_edge_mono; [exact/fin_hom_ofK | exact/homf].
  apply/(eq_in_nodes_bij _ labf)=> //; last exact/fin_hom_ofK.  
  apply/(lab_mono_eq _ labf); [exact/fin_hom_ofK | exact/of_fin_hom_bot]. 
Qed. 

Lemma iso_emb f g h : 
  iso f g h -> emb f g h.
Proof. by move=> []. Qed.

Lemma iso_bhom f g h : 
  iso f g h -> bhom f g h.
Proof. by rewrite isoE=> [[]]. Qed.

Lemma iso_hom f g h : 
  iso f g h -> hom f g h.
Proof. by move=> /iso_bhom/bhom_hom. Qed.

Lemma iso_ihom f g h : 
  iso f g h -> ihom f g h.
Proof. by move=> /iso_bhom/bhom_ihom. Qed.

Lemma iso_hom_le g h : 
  iso_eqv g h -> hom_le g h.
Proof. by move=> /iso_eqvP[f] /iso_hom ?; apply/hom_leP; exists f. Qed.

Lemma iso_ihom_le g h : 
  iso_eqv g h -> ihom_le g h.
Proof. by move=> /iso_eqvP[f] /iso_ihom ?; apply/ihom_leP; exists f. Qed.

Lemma iso_bhom_le g h : 
  iso_eqv g h -> bhom_le g h.
Proof. by move=> /iso_eqvP[f] /iso_bhom ?; apply/bhom_leP; exists f. Qed.

Lemma iso_emb_le g h : 
  iso_eqv g h -> emb_le g h.
Proof. by move=> /iso_eqvP[f] /iso_emb ?; apply/emb_leP; exists f. Qed.

Lemma iso_comp f f' g h j : 
  iso f g h -> iso f' h j -> iso (f' \o f) g j.
Proof. 
  rewrite !isoE=> [] [bhomf embf] [??]. 
  split; [exact/(bhom_comp bhomf)|exact/(emb_comp embf)].
Qed.

Lemma iso_eqv_refl : 
  reflexive (@iso_eqv T L).
Proof. by move=> g; apply/iso_eqvP; exists id; split=> //; exists id. Qed.

Lemma emb_le_trans : 
  transitive (@iso_eqv T L).
Proof. 
  move=> ??? /iso_eqvP[f] isof /iso_eqvP[g] ?. 
  apply/iso_eqvP; exists (g \o f); exact/(iso_comp isof).
Qed.

End Iso.

Section FPermIso.
Implicit Types (f : {fperm T}).

Lemma perm_iso f g h :
  emb f g h -> iso f g h.
Proof. move=> [??]; split=> //; exact/onW_bij/fperm_bij. Qed.

Lemma fsg_rename_iso f g : 
  iso f g (fsg_rename f g).
Proof. exact/perm_iso/fsg_rename_emb. Qed.

Lemma fsg_rename_isoP f g h : well_restricted g -> well_restricted h ->
  reflect (iso f g h) (h == fsg_rename f g).
Proof. 
  move=> wrg wrh; apply/(equivP eqP); split=> [->|]; first exact/fsg_rename_iso.
  move=> [labf monf bijf]; apply/eqP/fsgraphP; split=> [x | x y].
  - by rewrite fsg_rename_labE /= -labf inv_fpermK.
  move: monf=> /(edge_monoS wrg wrh labf)=> monf.
  by rewrite fsg_renameE /= -monf !inv_fpermK. 
Qed.

End FPermIso.

End Theory.
End Theory.

End Iso.

End FsGraph.
