From RelationAlgebra Require Import lattice monoid rel boolean.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From mathcomp Require Import eqtype choice order finfun fintype.
From mathcomp Require Import generic_quotient.
From eventstruct Require Import utils inhtype lposet.

(******************************************************************************)
(* This file provides a theory of pomset languages.                           *)
(* TODO                                                                       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.
Import Order.LTheory.

Local Open Scope order_scope.
Local Open Scope quotient_scope.
Local Open Scope ra_terms.
Local Open Scope lposet_scope.

Declare Scope pomset_scope.
Delimit Scope pomset_scope with pomset.

Local Open Scope pomset_scope.

Module Pomset.

Section lFinposet. 

Definition lfinposet_prod (E : finType) (L : eqType) := 
  ({ffun E -> L} * {ffun E * E -> bool} * {ffun E * E -> bool})%type.

Definition lfinposet_pred E L (p : lfinposet_prod E L) := 
  let lab := p.1.1 in
  let le  := p.1.2 in
  let lt  := p.2   in
  [&& [forall x, forall y, lt (x, y) == (y != x) && le (x, y)],
      [forall x, le (x, x)], 
      [forall x, forall y, le (x, y) && le (y, x) ==> (x == y)] 
    & [forall x, forall y, forall z, le (x, y) && le (y, z) ==> le (x, z)] 
  ].

Structure lfinposet E L := 
  { lfposet :> lfinposet_prod E L; _ : lfinposet_pred lfposet }.

Canonical lfinposet_subType E L := Eval hnf in [subType for (@lfposet E L)].

Definition lfinposet_eqMixin E L := 
  Eval hnf in [eqMixin of (lfinposet E L) by <:].
Canonical lfinposet_eqType E L := 
  Eval hnf in EqType (lfinposet E L) (lfinposet_eqMixin E L).

Definition lfinposet_choiceMixin E (L : choiceType) :=
  Eval hnf in [choiceMixin of (lfinposet E L) by <:].
Canonical lfinposet_choiceType E (L : choiceType) :=
  Eval hnf in ChoiceType (lfinposet E L) (lfinposet_choiceMixin E L).

Definition lfinposet_countMixin E (L : countType) :=
  Eval hnf in [countMixin of (lfinposet E L) by <:].
Canonical lfinposet_countType E (L : countType) :=
  Eval hnf in CountType (lfinposet E L) (lfinposet_countMixin E L).

Canonical subFinfun_subCountType E (L : countType) :=
  Eval hnf in [subCountType of (lfinposet E L)].

Definition lfinposet_finMixin E (L : finType) :=
  Eval hnf in [finMixin of (lfinposet E L) by <:].
Canonical lfinposet_finType E (L : finType) :=
  Eval hnf in FinType (lfinposet E L) (lfinposet_finMixin E L).

Canonical lfinposet_subFinType E (L : finType) :=
  Eval hnf in [subFinType of (lfinposet E L)].

End lFinposet.

End Pomset.

Implicit Types (L : Type).

Import lPoset.Syntax.

Definition iso_inv {L} (P : lPoset.eventType L -> Prop) := 
  forall (E1 E2 : lPoset.eventType L) (f : {iso E1 -> E2}), P E1 -> P E2.

Record lang L := Lang { 
  apply : lPoset.eventType L -> Prop;
  _     : iso_inv apply;
}.

Module Export Exports.
Coercion apply : lang >-> Funclass.
End Exports.

Module Lattice.
Section Lattice.

Context {L : Type}.
Implicit Types (P Q : lang L).

Definition leq P Q := lattice.leq (P : lPoset.eventType L -> Prop) Q.

Definition weq P Q := lattice.weq (P : lPoset.eventType L -> Prop) Q.

Lemma botP : iso_inv (lattice.bot : lPoset.eventType L -> Prop).
Proof. done. Qed.
Canonical bot := Lang (@botP).

Lemma topP : iso_inv (lattice.top : lPoset.eventType L -> Prop).
Proof. done. Qed.
Canonical top := Lang (@topP).

Lemma cupP P Q : iso_inv ((P : lPoset.eventType L -> Prop) ⊔ Q).
Proof. 
  move: P Q=> [] P + [] Q + p q /=.
  rewrite /iso_inv=> HP HQ f []. 
  - by move: (HP _ _ f)=> /[apply] ?; left. 
  by move: (HQ _ _ f)=> /[apply] ?; right. 
Qed.
Canonical cup P Q := Lang (@cupP P Q).

Lemma capP P Q : iso_inv ((P : lPoset.eventType L -> Prop) ⊓ Q).
Proof. 
  move: P Q=> [] P + [] Q + p q /=.
  rewrite /iso_inv=> HP HQ f []. 
  move: (HP _ _ f)=> /[apply] /[swap].
  by move: (HQ _ _ f)=> /[apply] /[swap].
Qed.
Canonical cap P Q := Lang (@capP P Q).

Lemma negP P : iso_inv (neg (P : lPoset.eventType L -> Prop)).
Proof. 
  move: P=> [] P + p q /=.
  rewrite /iso_inv=> HP f.
  apply/contra_not.
  by move: (HP _ _ (lPoset.Iso.Build.inv f)).
Qed.  
Canonical neg P := Lang (@negP P).

End Lattice.

Module Export Exports.

Canonical Structure pomset_lang_lattice_ops L : lattice.ops := 
  lattice.mk_ops (lang L) leq weq cup cap neg bot top.

Global Instance pomset_lang_lattice_morph L : 
  lattice.morphism BDL (@apply L).
Proof. by constructor. Qed.

Global Instance pomset_lang_lattice_laws L : 
  lattice.laws (BDL+STR+CNV+DIV) (@pomset_lang_lattice_ops L).
Proof.
  have H: (lattice.laws BDL (@pomset_lang_lattice_ops L)). 
  - by apply/(laws_of_injective_morphism (@apply L)).
  by constructor; apply H. 
Qed.

End Exports.

End Lattice.

Export Lattice.Exports.

Module Export Def.
Section Def.

Context {L : Type}.
Implicit Types (P Q : lang L) (p q : lPoset.eventType L).

Definition extensible P Q : Prop := 
  forall (p q : lPoset.eventType L) (f : {hom p -> q}), P p -> Q q -> (P ⊓ Q) (lPoset.ext f).

Definition stronger P Q : Prop := 
  forall p, P p -> exists q, Q q /\ inhabited {hom q -> p}.

(* uniformly stronger *)
Definition unistronger P Q : Prop := 
  forall p, P p -> exists q, Q q /\ inhabited {bhom q -> p}.

Definition supported P Q : Prop := 
  forall p, P p -> exists q, Q q /\ inhabited {bhom p -> q}.

(* TODO: generalize stronger/supported to arbitary relation on posets 
 *   and introduce notation in the style of `homo` from `ssreflect`:
 *   e.g. {lang P ⊑ Q : p q / p ~> q }
 *)

End Def.
End Def.

Module Export Syntax.
Notation "P ⊑ Q" := (stronger P Q) (at level 69) : pomset_scope.
Notation "P !⊑ Q" := (unistronger P Q) (at level 69) : pomset_scope.
Notation "P ↪ Q" := (supported P Q) (at level 50) : pomset_scope.
End Syntax.

Module Export Theory.
Section Theory.

Context {L : Type}.
Implicit Types (P Q R : lang L).

Lemma lang_iso_inv P : iso_inv P.
Proof. by case: P. Qed.

Lemma stronger_subset P Q :
  P ≦ Q -> P ⊑ Q. 
Proof. 
  move=> Hs p Hp; exists p; split; first exact /Hs.
  constructor; exact/[hom of idfun]. 
Qed.
  
Lemma stronger_refl P : 
  P ⊑ P.
Proof. 
  move=> p HP; exists p; split=> //. 
  constructor; exact/[hom of idfun].
Qed.

Lemma stronger_trans P Q R : 
  P ⊑ Q -> Q ⊑ R -> P ⊑ R.
Proof. 
  move=> H1 H2 p HP. 
  move: (H1 p HP)=> [q [HQ [f]]].
  move: (H2 q HQ)=> [r [HR [g]]].
  exists r; split=> //; constructor. 
  exact/[hom of f \o g].
Qed.

Lemma unistronger_subset P Q :
  P ≦ Q -> P !⊑ Q. 
Proof. 
  move=> Hs p Hp; exists p; split; first exact /Hs. 
  constructor; exact/[bhom of idfun]. 
Qed.
  
Lemma unistronger_refl P : 
  P !⊑ P.
Proof. 
  move=> p HP; exists p; split=> //. 
  constructor; exact/[bhom of idfun].
Qed.

Lemma unistronger_trans P Q R : 
  P !⊑ Q -> Q !⊑ R -> P !⊑ R.
Proof. 
  move=> H1 H2 p HP. 
  move: (H1 p HP)=> [q [HQ [f]]].
  move: (H2 q HQ)=> [r [HR [g]]].
  exists r; split=> //; constructor.
  exact/[bhom of f \o g].
Qed.

Lemma unistronger_stronger P Q : 
  P !⊑ Q -> P ⊑ Q.
Proof. 
  move=> H p HP. 
  move: (H p HP)=> [q [HQ [f]]].
  exists q; split=> //; constructor; exact/f. 
Qed.

Lemma supported_subset P Q :
  P ≦ Q -> P ↪ Q. 
Proof. 
  move=> Hs p Hp; exists p; split; first exact /Hs.
  constructor; exact/[bhom of idfun]. 
Qed.

Lemma supported_refl P : 
  P ↪ P. 
Proof. 
  move=> p HP; exists p; split=> //.
  constructor; exact/[bhom of idfun].
Qed.

Lemma supported_trans P Q R : 
  (P ↪ Q) -> (Q ↪ R) -> (P ↪ R). 
Proof. 
  move=> H1 H2 p HP. 
  move: (H1 p HP)=> [q [HQ [f]]].
  move: (H2 q HQ)=> [r [HR [g]]].
  exists r; split=> //; constructor. 
  exact/[bhom of g \o f].
Qed.

End Theory.
End Theory.

End Pomset.

Export Pomset.Exports.
Export Pomset.Lattice.Exports.
Export Pomset.Def.
Export Pomset.Syntax.
Export Pomset.Theory.


Module LinPomset.

Module Export Lang. 
Section Lang. 
Context {L : Type}.

Definition prop (E : lPoset.eventType L) : Prop := 
  total (<=%O : rel E).

Lemma iso_inv : Pomset.iso_inv prop. 
Proof. 
  rewrite /prop=> E1 E2 f T e1 e2. 
  set (g := lPoset.Iso.Build.inv f).
  move: (T (g e1) (g e2)).
  case H: (g e1 <= g e2); move: H. 
  - by rewrite (ca_reflecting g)=> ->.
  by move=> ? /=; rewrite (ca_reflecting g)=> ->.    
Qed.

Definition lang : Pomset.lang L := 
  Pomset.Lang iso_inv.

End Lang. 
End Lang.

Notation lang := (Lang.lang).

Module Export Theory.
Section Theory.

Context {L : Type}.

(* TODO: introduce a way to create linearly ordered set 
 *   from a proof that partially ordered set is totally ordered,  
 *   i.e. make a conversion from `p : lPoset.eventType L` and 
 *   a proof of `lLoset.lang p` to `lLoset.eventType L` 
 *)

End Theory.
End Theory.

End LinPomset.


Module Export Schedule.

Import lPoset.Hom.Syntax.
Import lPoset.bHom.Syntax.
Import lPoset.Iso.Syntax.

Module Schedule. 
Section Schedule. 
Context {L : Type} (E : lPoset.eventType L).

Definition prop (E' : lPoset.eventType L) : Prop := 
  LinPomset.lang E' /\ inhabited ({bhom E -> E'}).

Lemma iso_inv : Pomset.iso_inv prop. 
Proof. 
  move=> E1 E2 f [] HT [g]; repeat split.
  - by apply /(LinPomset.Lang.iso_inv f).  
   by apply /[bhom of f \o g].
Qed.

Definition lang : Pomset.lang L := 
  Pomset.Lang iso_inv. 

End Schedule. 
End Schedule.

Notation schedule := (Schedule.lang).

Module Scheduling. 
Section Scheduling. 
Context {L : Type} (P : Pomset.lang L).

Definition prop : lPoset.eventType L -> Prop := 
  fun q => exists p, P p /\ P q /\ schedule p q.

Lemma iso_inv : Pomset.iso_inv prop. 
Proof. 
  move=> E1 E2 f [] E1' [] HP' [HP [Hl [g]]].
  exists E1'; repeat split=> //=.
  - by apply /(lang_iso_inv f HP).
  - by apply /(LinPomset.Lang.iso_inv f).
  by apply /[bhom of f \o g].
Qed.

Definition lang : Pomset.lang L := 
  Pomset.Lang iso_inv. 

End Scheduling. 
End Scheduling. 

Notation scheduling := (Scheduling.lang).

Section Def.
Context {L : Type}.
Implicit Types (P : Pomset.lang L).

Definition schedulable P : Prop := 
  P ↪ P ⊓ @LinPomset.lang L.

End Def.

Section Theory. 
Context {L : Type}. 
Implicit Types (P Q : Pomset.lang L). 
Implicit Types (p q : lPoset.eventType L).

Lemma schedule_inh P p : 
  schedulable P -> P p -> inhabited { q | schedule p q }. 
Proof. 
  move=> Hd Hp; move: (Hd p Hp). 
  move=> [] p' [] [] Hp' Hl [] f. 
  constructor; exists p'=> //=. 
Qed.  

Lemma schedule_bij p q : 
  {bhom p -> q} -> schedule q ≦ schedule p.
Proof. 
  move=> f p' [Hl [g]]; repeat constructor=> //. 
  exact /[bhom of g \o f]. 
Qed.

Lemma schedule_hom P Q p q : extensible P Q -> schedulable P -> 
  P p -> Q q -> ({hom p -> q}) -> Q ⊓ schedule q ⊑ P ⊓ schedule p.
Proof. 
  (* For the proof of this lemma, we need to construct 
   * a (decidable) linear extension of an arbitary partial order. 
   * It is not possible to do this **constructively** in general. 
   * It should be possible, however, under additional assumptions 
   * on partial order. There are several directions we can take.
   *
   *  (1) Trivially, it is possible to construct linear extension 
   *      for partial order over finite type.  
   *
   *  (2) It is possible for a finitely supported partial order over countable type.
   *
   *  (3) For a countable type if the partial order is embedded in
   *      the total order induced by embedding into natural numbers.
   *      That is `r x y -> x <=^n y`. 
   *      Under this assumption there is a very simple way to extend 
   *      the partial order to linear order: 
   *      just link the elements unrelated by `r` according to their `<=^n` ordering. 
   * 
   *  (4) It can also be done for a partial order over countable type 
   *      with finite width (width is the size of the largest antichain). 
   *  
   *  The (1) approach should work nicely for finite pomsets. 
   *  For finitely supported pomsets we can actually combine (2) and (3). 
   *  Since we are going to use finitly supported pomsets for operational semantics
   *  we can enforce the axiom required by (3). 
   *  As for (4) it is not obvious how it can be exploited in practice.
   *)
  move=> He Hd Hp Hq f q' [] Hq' [Hl [g]].
  pose h := [hom of g \o f].
  pose p' := lPoset.ext h. 
  move: (He _ _ h) Hp Hq'=> /[apply] /[apply] [[]] + _. 
  move: (Hd p')=> /[apply] [[]] p'' [] [] Hp'' HL [] k.
  exists p''; repeat split=> //.
  - apply/(comp_bhom k _)/lPoset.Ext.bhom.
  pose h' := (lPoset.Ext.hom h).
  pose k' := (lPoset.bHom.invF k).
  exists (h' \o k').
  repeat constructor.
  - by move=> x /=; rewrite (lab_preserving h) -(inv_lab k).
  move=> e1 e2=> /= /(ca_img_inv k) /orP[].
  - by move=> /(ca_monotone h').
  move=> /ext_incomp /orP[]. 
  - by subst h k'; move=> /= /eqP->. 
  rewrite /comparable.
  move: Hl=> /=; rewrite /LinPomset.Lang.prop=> Ht.
  by move: (Ht (h (k' e1)) (h (k' e2)))=> ->. 
Qed.

Lemma scheduling_subset P Q : 
  P ≦ Q -> scheduling P ≦ scheduling Q.
Proof. 
  move=> H p' [p [Hp [Hp' Hs]]].
  exists p; split=> //; first exact/H.
  split=> //; exact/H. 
Qed.

Lemma scheduling_unistronger P Q : extensible Q P -> 
  P !⊑ Q -> scheduling P ≦ scheduling Q.
Proof. 
  move=> He Hw p' [p [Hp [Hp']]].
  move=> /[dup] Hs [Hl [f]].
  move: (Hw p Hp)=> [q [Hq [g]]].
  exists q; split=> //; split; last first. 
  - by apply/(schedule_bij g). 
  pose h  := [bhom of f \o g].
  pose q' := lPoset.ext h. 
  pose j  := (lPoset.Ext.iso h).
  apply /(lang_iso_inv j).
  by apply /(fst (He q p' h Hq Hp')).
Qed.  

Lemma scheduling_stronger P Q : extensible Q P -> schedulable Q -> 
  P ⊑ Q -> scheduling P ⊑ scheduling Q.
Proof. 
  move=> He Hd Hw p' [p [Hp Hs]]. 
  move: (Hw p Hp)=> [q [Hq [f]]].
  move: (@schedule_hom Q P q p He Hd Hq Hp f)=> H.
  move: (H p' Hs)=> [q' []] [Hq' [Hs' [g]]].
  exists q'; split=> //=.
  exists q; repeat split=> //.
Qed.

End Theory.  

End Schedule.
