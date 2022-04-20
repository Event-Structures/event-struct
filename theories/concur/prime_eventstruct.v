From RelationAlgebra Require Import lattice boolean.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From mathcomp Require Import eqtype choice order finmap fintype fingraph.
From mathcomp Require Import generic_quotient zify.
From mathcomp.tarjan Require Import extra acyclic kosaraju acyclic_tsorted. 
From eventstruct Require Import pomset utils relalg order lposet ident rel.
From eventstruct Require Import inhtype.

(******************************************************************************)
(* This file provides a theory of prime event structures.                     *)
(* Prime event structure inherits partial causality order from pomset and     *)
(* also has binary conflict relation (symmetric and irreflexive).             *)
(*                                                                            *)
(*       Prime.eventStruct E == the type of prime event structures with       *)
(*                              binary conflict, consisting of                *)
(*                              a causality relation <= (a partial order),    *)
(*                              and a binary conflict relation # (irreflexive *)
(*                              and symmetric).                               *)
(*       Prime.eventType d   == a type of events, i.e. a type equipped with   *)
(*                              prime event structure instance.               *)
(*       Prime.cfg d es x    == a predicate asserting that subset of events x *)
(*                              given as decidable predicate) forms a         *)
(*                              configuration of the event structure es.      *)
(*                              Configuration is a causally-closed and        *)
(*                              conflict-free subset of events.               *)
(*       PrimeG.eventStruct E == the type of prime event structures with      *)
(*                               general conflict, consisting of              *)
(*                               a causality relation <= (a partial order),   *)
(*                               and a general conflict predice gcf over      *)
(*                               finite subset of events.                     *)
(*                               and symmetric).                              *)
(*       PrimeG.eventType d   == a type of events, i.e. a type equipped with  *)
(*                               prime event structure instance.              *)
(*       PrimeG.cfg d es x    == a predicate asserting that subset of events  *)
(*                               x (given as decidable predicate) forms a     *)
(*                               configuration of the event structure es.     *)
(*                               Configuration is a causally-closed and       *)
(*                               conflict-free subset of events.              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.LTheory.
Local Open Scope order_scope.
Local Open Scope fset_scope.
Local Open Scope quotient_scope.

(* a hack to bypass a shadowing problem caused by relation-algebra import *)
Local Notation symmetric  := Coq.ssr.ssrbool.symmetric.
Local Notation transitive := Coq.ssr.ssrbool.transitive.

Declare Scope prime_eventstruct_scope.
Delimit Scope prime_eventstruct_scope with prime_es.
Local Open Scope prime_eventstruct_scope.

Reserved Notation "x \# y" (at level 75, no associativity).

Definition hereditary {T : Type} (ca cf : rel T) := 
  forall x y z : T, cf x y -> ca y z -> cf x z.

Module PrimeC.

Module EventStruct.
Section ClassDef.

Record mixin_of (E0 : Type) (L : Type) (b : lPoset.lPoset.class_of E0 L)
                (E := lPoset.lPoset.Pack b) := Mixin {
  cons : pred {fset E};

  _ : cons fset0;
  (* TODO: remove single-event consistency axiom? *)
  _ : forall (e : E), cons [fset e];
  _ : forall (X Y : {fset E}), X `<=` Y -> cons Y -> cons X;
  _ : forall X e e', e <= e' -> cons (e' |` X) -> cons (e |` X)
}.

Set Primitive Projections.
Record class_of (E L : Type) := Class {
  (* TODO: use lDwFinPoset.class_of *)
  (* TODO: simplify hierarchy? make lPoset subclass 
   *   with Ident type inheritance  
   *)
  base   : lPoset.lPoset.class_of E L;
  mixin1 : DwFinPOrder.DwFinPOrder.mixin_of base;
  mixin2 : Countable.mixin_of E;
  mixin3 : Ident.mixin_of (Countable.Class base mixin2);
  mixin4 : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> lPoset.lPoset.class_of.

Local Coercion base2 E L (c : class_of E L) : 
  DwFinPOrder.DwFinPOrder.class_of E := 
    DwFinPOrder.DwFinPOrder.Class (mixin1 c).

Local Coercion base3 E L (c : class_of E L) : 
  Ident.class_of E := Ident.Class (mixin3 c).

Structure type (L : Type) := Pack { sort; _ : class_of sort L }.

Local Coercion sort : type >-> Sortclass.

Variables (E : Type) (L : Type) (cT : type L).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') L in c.
Definition clone c of phant_id class c := @Pack E L c.
(* Definition clone_with disp' c of phant_id class c := @Pack disp' T c. *)

Definition pack :=
  fun bE b & phant_id (@lPoset.lPoset.class L bE) b =>
  fun m1 m2 m3 m4 => Pack (@Class E L b m1 m2 m3 m4).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
(* TODO: countType missing *)
Definition identType := @Ident.Pack cT class.
Definition porderType := @Order.POrder.Pack tt cT class.
Definition dwFinPOrderType := @DwFinPOrder.DwFinPOrder.Pack cT class.
Definition lposetType := @lPoset.lPoset.Pack L cT class.
End ClassDef.

Module Export Exports.
Coercion base : class_of >-> lPoset.lPoset.class_of.
Coercion base2 : class_of >-> DwFinPOrder.DwFinPOrder.class_of.
Coercion base3 : class_of >-> Ident.class_of.
Coercion mixin1 : class_of >-> DwFinPOrder.DwFinPOrder.mixin_of.
Coercion mixin2 : class_of >-> Countable.mixin_of.
Coercion mixin3 : class_of >-> Ident.mixin_of.
Coercion mixin4 : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> Order.POrder.type.
Coercion dwFinPOrderType : type >-> DwFinPOrder.DwFinPOrder.type.
Coercion lposetType : type >-> lPoset.eventType.
Coercion identType  : type >-> Ident.type.
Canonical eqType.
Canonical choiceType.
Canonical identType.
Canonical porderType.
Canonical dwFinPOrderType.
Canonical lposetType.
End Exports.

End EventStruct.

Export EventStruct.Exports.

Notation eventType := EventStruct.type.
Notation eventStruct := EventStruct.class_of.
Notation EventType E L m := (@EventStruct.pack E L _ _ id m).

Module Export Def.
Section Def.

Variable (L : Type) (E : eventType L).

Definition cons : pred {fset E} :=
  EventStruct.cons (EventStruct.class E).

Definition gcf : pred {fset E} := 
  fun C => ~~ cons C.

Definition cf : rel E := 
  fun e1 e2 => gcf [fset e1; e2].

Definition cf_free (p : pred E) := 
  forall (s : {fset E}), {subset s <= p} -> cons s.

Definition cfg (p : pred E) := 
  dw_closed p /\ cf_free p.

(* TODO: rename? *)
Definition wcons : pred {fset E} := 
  [pred X | cons X && (#|` X| != 1)%N].

End Def.
End Def.

Prenex Implicits cons gcf cf.

Module Export Syntax.
Notation "x \# y" := (cf x y) : prime_eventstruct_scope.
End Syntax.

Module Export Theory.
Section Theory.
Context {L : Type} {E : eventType L}.
Implicit Types (e : E) (X Y : {fset E}).

Lemma cons_self e : cons [fset e].
Proof. by move: e; case: E => ? [?] ??? []. Qed.

Lemma cons0 : cons (fset0 : {fset E}).
Proof. by case: E => ? [?] ??? []. Qed.

(* TODO: rename `cons_contra`? *)
Lemma cons_contra X Y : X `<=` Y -> cons Y -> cons X.
Proof. by move: X Y; case: E => ? [?] ??? []. Qed.

Lemma cons_prop X e1 e2 : 
  e1 <= e2 -> cons (e2 |` X) -> cons (e1 |` X).
Proof. by move: X e1 e2; case: E => ? [?] ??? []. Qed.

Lemma gcf_self e : ~~ (gcf [fset e]).
Proof. rewrite /gcf negbK; exact/cons_self. Qed.

Lemma gcf_ext X Y : X `<=` Y -> gcf X -> gcf Y.
Proof. by rewrite /gcf=> /cons_contra /contra. Qed.

Lemma gcf_hered X e1 e2 : 
  e1 <= e2 -> gcf (e1 |` X) -> gcf (e2 |` X).
Proof. by rewrite /gcf=> /cons_prop /contra /[apply]. Qed.

Lemma cf_irrefl : irreflexive (cf : rel E).
Proof. 
  move=> e; rewrite /cf fsetUid; apply/eqP.
  rewrite eqbF_neg; exact/gcf_self.
Qed.

Lemma cf_sym : symmetric (cf : rel E).
Proof. by move=> e1 e2; rewrite /cf fsetUC. Qed.

Lemma cf_hered : hereditary (<=%O) (cf : rel E).
Proof. 
  move=> e1 e2 e3 /[swap]; rewrite /cf. 
  rewrite [in [fset e1; e2]]fsetUC [in [fset e1; e3]]fsetUC.
  exact/gcf_hered.
Qed.

(* TODO: better name? *)
Lemma cf_hered2 e1 e1' e2 e2' : 
  e1 \# e2 -> e1 <= e1' -> e2 <= e2' -> e1' \# e2'.
Proof. 
  move=> cf12 ca1 ca2; apply/(cf_hered _ ca2).
  rewrite cf_sym; apply/(cf_hered _ ca1).
  by rewrite cf_sym.
Qed.

Lemma cf_gcf X e1 e2 : 
  e1 \in X -> e2 \in X -> e1 \# e2 -> gcf X.
Proof. 
  move=> in1 in2 cf12.
  apply/(gcf_ext _ cf12). 
  rewrite fsubUset !fsub1set; exact/andP.
Qed.

Lemma cons_ca_contra (X Y : {fset E}) :
  {subsumes X <= Y : x y / x <= y} -> cons Y -> cons X.
Proof.
  move: X {2}(X `\` Y) (@erefl _ (X `\` Y))=> /[swap].
  elim/fset_ind=> [?/eqP/[! fsetD_eq0]/cons_contra//|].
  move=> x ?? IHxy X XYE /[dup] S + cY; rewrite -(@fsetD1K _ x X); last first.
  - move/fsetP/(_ x): XYE; rewrite ?inE eqxx andbC /=; by case: (x \in X).
  case/(_ x)=> [/[! (inE, eqxx)]//|y ? /cons_prop]; apply.
  apply: IHxy=> // [|?]; last first.
  - rewrite ?inE=> /orP[/eqP->|/andP[_ /S //]]; by exists y.
  rewrite fsetDUl fsetDDl [x |` _]fsetUC -fsetDDl XYE fsetDUl.
  have/eqP->: ([fset y] `\` Y == fset0) by rewrite fsetD_eq0 fsub1set.
  by rewrite fsetDv ?fset0U mem_fsetD1.
Qed.

Lemma prefix_ca_closed (e : E) : dw_closed (<= e).
Proof. move=> e1 e2 /=; exact: le_trans. Qed.

Lemma prefix_cf_free e : cf_free (<= e).
Proof. 
  move=> X S; apply/(@cons_ca_contra _ [fset e])/cons_self.
  move=> x i; exists e; rewrite ?inE //; exact/S.
Qed.

Lemma prefix_cfg e : cfg (<= e).
Proof. split; [exact/prefix_ca_closed | exact/prefix_cf_free]. Qed.

Lemma cf_free_fset (X : {fset E}) : reflect (cf_free (mem X)) (cons X).
Proof. apply/(iffP idP)=> [?? /fsubsetP/cons_contra|]; exact. Qed.

Lemma cfg0 : cfg (mem (fset0 : {fset E})).
Proof.
  split=> [> /=|]; first by rewrite inE.
  apply/cf_free_fset/cons0.
Qed.

End Theory.
End Theory.

Module Export Lang.

(* TODO: restructure submodules/sections *)
Section lFsPrePosetOf.

(* TODO: (L bot E) order of arguments contradicts (E L bot) in pomset.v *)
Context {L : botType} {E : eventType L}.
Context (X : {fset E}).
Implicit Types (e : E).

Hypothesis lab_def : [forall x : X, lab (val x) != bot].

Definition lfspreposet_of := 
  @lFsPrePoset.build_cov E L X lab (<=%O : rel E).

Lemma lfspreposet_of_finsupp : 
  lfsp_eventset lfspreposet_of = X.
Proof. exact/lFsPrePoset.build_eventset/forallP. Qed.

Lemma lfspreposet_of_mixin :
  supp_closed lfspreposet_of && acyclic (fin_ica lfspreposet_of).
Proof.
  apply/andP; split.
  - by apply/lFsPrePoset.supp_closed_build/forallP.
  apply/lFsPrePoset.build_cov_acyclic; last first.
  - move=> /=; exact/le_trans.
  - move=> /=; exact/le_anti.
  - move=> /=; exact/le_refl.
  exact/forallP.    
Qed.

End lFsPrePosetOf.

Section lFsPosetOf.
Context {L : botType}.

Definition lfsposet_of (E : eventType L) (X : {fset E}) : lfsposet E L :=
  if eqP is ReflectT p then
    mklFsPoset (@lfspreposet_of_mixin L E X p)
  else (lFsPoset.empty E L).

Context (E : eventType L) (X : {fset E}).

Lemma lfsposet_of0 : 
  lfsposet_of (fset0 : {fset E}) = lFsPoset.empty E L.
Proof.
  rewrite /lfsposet_of /lfspreposet_of; case: eqP=> // ?.
  apply/eqP/lfspreposet_eqP; split=>>; rewrite /lFsPoset.empty /=.
  - rewrite lFsPrePoset.fs_lab_empty lFsPrePoset.build_lab /sub_lift.
    by case: insubP.
  rewrite lFsPrePoset.fs_ica_empty lFsPrePoset.build_ica /sub_rel_lift /=.
  by case: insubP.
Qed.

Lemma lfsposet_of_emp : 
  [forall x : X, lab (val x) != bot] <> true ->
  lfsposet_of X = (lFsPoset.empty E L).
Proof. by rewrite /lfsposet_of; case: eqP. Qed.

Hypothesis lab_def : [forall x : X, lab (val x) != bot].

Lemma lfsposet_of_val : 
  lfsposet_of X = lfspreposet_of X :> lfspreposet E L.
Proof. by rewrite /lfsposet_of; case: eqP=> // *. Qed.

Lemma lfsposet_of_eventset :
  lfsp_eventset (lfsposet_of X) = X.
Proof. by rewrite lfsposet_of_val lfspreposet_of_finsupp. Qed.

Lemma lfsposet_of_lab :
  {in X, fs_lab (lfsposet_of X) =1 lab}.
Proof.
  rewrite lfsposet_of_val=> ??.
  rewrite /lfspreposet_of /= lFsPrePoset.build_lab /sub_lift.
  by case: insubP=> //= [??->|/negP].
Qed.

Lemma lfsposet_of_fin_ca :
  fin_ca (lfsposet_of X) =2 relpre val (<=%O : rel E).
Proof. 
  rewrite lfsposet_of_val /lfspreposet_of=> ??.
  rewrite lFsPrePoset.build_cov_fin_ca //; last first.
  - move=> /=; exact/le_trans.
  - move=> /=; exact/le_anti.
  exact/forallP.      
Qed.

End lFsPosetOf.

Lemma lfsposet_of0_eventset {L : botType} (E : eventType L) : 
  lfsp_eventset (@lfsposet_of L E (fset0 : {fset E})) = fset0.
Proof. 
  rewrite lfsposet_of_val; last (apply/forallP; case)=> //.
  by rewrite lFsPrePoset.build_eventset //; case.  
Qed.

Definition pomset_lang {L : botType} (E : eventType L) := 
  fun (p : pomset E L) => 
    exists2 X : {fset E}, cfg (mem X) & p = \pi (lfsposet_of X).

End Lang.


Module Export Hom.

Module Hom.
Section ClassDef. 
(* TODO: homomorphism between pomsets labelled by different labels? *)
Context {L : Type} (E1 E2 : eventType L).
Implicit Types (f : E1 -> E2).

Definition axiom f := 
  [/\ { mono f : e / lab e }
    , { homo pideal f }
    & { homo (@!f) : X / wcons X } 
  ].

Structure type := Pack { apply ; _ : axiom apply }.

Local Coercion apply : type >-> Funclass.

Definition mk h mkH : type :=
  mkH (let: Pack _ c := h return @axiom h in c).

Definition type_of (_ : phant (E1 -> E2)) := type.

End ClassDef.

Module Export Exports.
Coercion apply : type >-> Funclass.
End Exports.

End Hom.

Export Hom.Exports.

Module Export Syntax. 
Notation hom := Hom.type.
Notation "{ 'hom' T }" := 
  (@Hom.type_of _ _ _ (Phant T)) : prime_eventstruct_scope.
Notation "[ 'hom' 'of' f ]" := 
  (Hom.mk (fun hCls => @Hom.Pack _ _ _ f hCls))
  (at level 0, format "[ 'hom'  'of'  f ]") : prime_eventstruct_scope.
End Syntax.

Module Build.
Section Build.
Context {L : Type} {E E1 E2 E3 : eventType L}.
Implicit Types (f : {hom E2 -> E3}) (g : {hom E1 -> E2}).

Lemma id_axiom : Hom.axiom (@idfun E).
Proof. split=> //= e; rewrite ?imfset_id //. Qed.

Lemma comp_axiom f g : Hom.axiom (comp f g).
Proof.
  case f=> {}f [] labf idlf consf.
  case g=> {}g [] labg idlg consg.
  split=> //=.
  - by move=> e; rewrite labf labg.
  - exact/homo_pideal_comp.
  by move=> X; rewrite imfset_comp=> /consg /consf.
Qed.

End Build.

Module Export Exports.
Section Exports.
Context {L : Type} {E E1 E2 E3 : eventType L}.
Implicit Types (f : {hom E2 -> E3}) (g : {hom E1 -> E2}).

Canonical id_hom := Hom.Pack (@id_axiom L E).
Canonical comp_hom f g := Hom.Pack (comp_axiom f g).

End Exports.
End Exports. 

End Build.

Module Export Theory.
Section Theory. 
Context {L : botType} {E1 E2 : eventType L}.
Implicit Types (f : {hom E1 -> E2}).
Implicit Types (X : {fset E1}).

Lemma lab_preserving f :
  { mono f : e / lab e }.
Proof. by case: f=> ? [] /=. Qed.

Lemma wcons_mon f X : 
  wcons X -> wcons (f @` X).
Proof. case: f=> ? [] /= ??; exact. Qed.

Lemma cons_mon f X : 
  cons X -> cons (f @` X).
Proof.
  move=> c; case: (boolP (wcons X))=> [/(wcons_mon f)/andP[]|] //.
  rewrite /wcons /= negb_and c /= negbK=>/cardfs1P[?->].
  by rewrite imfset1 cons_self.
Qed.

Lemma gcf_mon f X : 
  gcf (f @` X) -> gcf X.
Proof. exact/contra/cons_mon. Qed.

Lemma cf_mon f e1 e2 :
  f e1 \# f e2 -> e1 \# e2.
Proof. 
  rewrite /cf=> ?; apply/(@gcf_mon f).
  by rewrite imfsetU !imfset1=> /=.
Qed.

(* TODO: move to order.v *)
Lemma hom_prefix f e1 e2 : 
  e1 <= f e2 -> exists2 e, e1 = f e & e <= e2.
Proof. 
  case: f=> {}f [] ? + ? /=. 
  rewrite homo_pidealE=> /(_ e2).
  rewrite /dw_surjective_le surj_rstE. 
  by move=> /[apply] [[]] /= e ??; exists e.
Qed. 

Lemma hom_cons_inj f X : 
  cons X -> {in X & X, injective f}.
Proof.
  move=> c e1 e2 ??.
  case: (boolP (wcons [fset e1; e2]))=> [/(wcons_mon f)/[swap] Ef|].
  - by rewrite imfsetU ?imfset1 /wcons /= cardfs2 Ef eqxx /= andbF.
  rewrite /wcons /= negb_and negbK cardfs2.
  case: (e1 =P e2)=> //= ? /orP[]// /negP[].
  by apply/(cons_contra _ c)/fsubsetP=>>; rewrite ?inE=>/orP[]/eqP->.
Qed.

(* TODO: try to change direction of arrows/morphisms to get rid of anti? *)
Lemma in_cons_ca_anti f X :
  cons X -> {in X & X, forall e1 e2, f e1 <= f e2 -> e1 <= e2}.
Proof.
  (* TODO: use dw_surj_le_in_ahomo_in lemma *)
  move=> c e1 e2 i ? /hom_prefix[x /[swap] l /(@hom_cons_inj f (x |` X))-> //].
  - by apply/(cons_prop l); rewrite mem_fset1U.
  all: by rewrite ?inE (i, eqxx).
Qed.

(* TODO: prove first on the level of `lfsposet_of`, 
 *   use subsumption notation
 *)
Lemma pomset_lang_sub f (p : pomset E1 L) :
  (forall x : E2, lab x != bot) ->
  pomset_lang p -> 
  exists2 q : pomset E2 L, pomset_lang q & bhom_le p q.
Proof.
  move=> ld2 [X [ccX cfX]].
  case: ([forall x : X, lab (val x) != bot] =P true); first last.
  - move/lfsposet_of_emp=>->->.
    exists (\pi (lFsPoset.empty E2 L)).
    + exists fset0; first exact/cfg0; by rewrite lfsposet_of0.
    rewrite pom_bhom_le -?lfsposet_of0; apply/lFinPoset.bHom.bhom_leP.
    (* have g: forall E E' : eventType L, *)
    (*         [FinEvent of @lfsposet_of L bot E  fset0] -> *)
    (*         [FinEvent of @lfsposet_of L bot E' fset0]. *)
    have g: forall E E' : eventType L,
            (* TODO: make arguments of (@lfsposet_of L bot E) implicit *)
            (lfsp_eventset (@lfsposet_of L E  (fset0 : {fset E}))) ->
            (lfsp_eventset (@lfsposet_of L E' (fset0 : {fset E'}))) .
    + by move=> ??; rewrite ?lfsposet_of0_eventset=> [[]].
    exists=> /=; exists (g E2 E1); do ? split=> /=.
    1,2: by move=> /[dup]; rewrite {1}lfsposet_of0_eventset=> [[]].
    by exists (g E1 E2)=> /[dup] /=; rewrite {1}lfsposet_of0_eventset=> [[]].
  move=> ld1 pE; exists (\pi (@lfsposet_of L E2 (f @` X))).
  - exists (f @` X)=> //; split; last exact/cf_free_fset/cons_mon/cfX.
    move=>> /[swap]/imfsetP[] /= x' /[swap]-> /[swap] /hom_prefix.
    case=> y' -> /ccX/[apply] ?; by apply/imfsetP; exists y'.
  rewrite pE pom_bhom_le.
  have ?: [forall x : (f @` X), lab (val x) != bot] by exact/forallP.
  have In: forall x : (lfsp_eventset (@lfsposet_of L E1 X)),
    f (val x) \in (lfsp_eventset (@lfsposet_of L E2 (f @` X))).
  - case=> /= x; rewrite ?lfsposet_of_eventset //. 
    by move=> ?; rewrite in_imfset.
  set g : 
    [FinEvent of (@lfsposet_of L E1 X)] -> 
    [FinEvent of (@lfsposet_of L E2 (f @` X))] := fun x => [` (In x)].
  (* TODO: use bhom_leP lemma? *)
  apply/lFinPoset.bHom.bhom_leP; exists=> /=. 
  have bijg : bijective g.
  - apply/inj_card_bij=> /=; last first.
    + rewrite -?cardfE !lfsposet_of_eventset //.
      exact/(leq_trans (leq_imfset_card _ _ _)).
    rewrite /g; case=> ? in1 [? in2 /=] /(congr1 val) /= /hom_cons_inj.
    move/(_ _ _ in1 in2)=> ev; apply/val_inj/ev/cfX=> ?.
    by rewrite lfsposet_of_eventset.
  exists (invFh bijg); split=> //; last exact/injFh_bij. 
  - case=> /= e /[dup]; rewrite {1}lfsposet_of_eventset // => ef ein.
    rewrite /g !fin_labE -?fin_lab_mono.
    move: ef=> /imfsetP[e'] /= ein' eqe'. 
    have ein'': e' \in lfsp_eventset (lfsposet_of X : lfsposet E1 L).
    + by rewrite @lfsposet_of_eventset.
    have->: [` ein] = g [` ein''].
    + by rewrite /g; apply/val_inj. 
    rewrite invFh_f /= !lfsposet_of_lab ?eqe' ?lab_preserving //.
    by apply/imfsetP; exists e'.
  apply/(cancel_le_ahomo_homo (f_invFh _)). 
  case=> ? /[dup] + ? [? /[dup]+?]. 
  rewrite {1 2}lfsposet_of_eventset // => ??.
  rewrite /g ?/(_ <= _) /=.
  rewrite !lfsposet_of_fin_ca //.
  move=> /(@in_cons_ca_anti f X). 
  apply=> //; exact/cfX.
Qed.

End Theory.
End Theory.

End Hom.

Module Export Iso.

Module Iso.
Section ClassDef. 
Context {L : Type} (E1 E2 : PrimeC.eventType L).
Implicit Types (f : E1 -> E2).

Definition axiom f := 
  [/\ { mono f : e / lab e }
    , { mono f : e1 e2 / e1 <= e2 }
    , { mono (@!f) : X / wcons X } 
    & bijective f
  ].

Structure type := Pack { apply ; _ : axiom apply }.

Local Coercion apply : type >-> Funclass.

Definition mk h mkH : type :=
  mkH (let: Pack _ c := h return @axiom h in c).

Definition type_of (_ : phant (E1 -> E2)) := type.

Lemma hom_axiom_of f : axiom f -> Hom.axiom f.
Proof. 
  move=> [] labf lef consf bijf; split=> //; last exact/monoW.
  apply/homo_pidealE/ahomo_dw_surj_le.
  - exact/mono2aW.
  exact/surj_dw_surj/bij_surj.
Qed.

Lemma lposet_iso_axiom_of f : axiom f -> lPoset.Iso.Iso.axiom f.
Proof. by move=> []. Qed.

Lemma iso_axiom_of f : lPoset.Iso.Iso.axiom f -> 
  { mono (@!f) : X / wcons X } -> axiom f.
Proof. by move=> [] *; split=> //. Qed.

Variables (cT : type).

Lemma homAxiom : Hom.axiom cT.
Proof. by case: cT=> /= ? /hom_axiom_of. Qed.

Lemma lposet_homAxiom : lPoset.Hom.Hom.axiom cT.
Proof. 
  case: cT=> /= ? /lposet_iso_axiom_of.
  exact/lPoset.Iso.Iso.hom_axiom_of. 
Qed.

Lemma lposet_ihomAxiom : lPoset.iHom.iHom.axiom cT.
Proof. 
  case: cT=> /= ? /lposet_iso_axiom_of.
  exact/lPoset.Iso.Iso.ihom_axiom_of. 
Qed.

Lemma lposet_bhomAxiom : lPoset.bHom.bHom.axiom cT.
Proof. 
  case: cT=> /= ? /lposet_iso_axiom_of.
  exact/lPoset.Iso.Iso.bhom_axiom_of. 
Qed.

Lemma lposet_embAxiom : lPoset.Emb.Emb.axiom cT.
Proof. 
  case: cT=> /= ? /lposet_iso_axiom_of.
  exact/lPoset.Iso.Iso.emb_axiom_of. 
Qed.

Lemma lposet_isoAxiom : lPoset.Iso.Iso.axiom cT.
Proof. by case: cT=> /= ? /lposet_iso_axiom_of. Qed.

Definition homType         := Hom.Pack homAxiom.
Definition lposet_homType  := lPoset.Hom.Hom.Pack lposet_homAxiom.
Definition lposet_ihomType := lPoset.iHom.iHom.Pack lposet_ihomAxiom.
Definition lposet_bhomType := lPoset.bHom.bHom.Pack lposet_bhomAxiom.
Definition lposet_embType  := lPoset.Emb.Emb.Pack lposet_embAxiom.
Definition lposet_isoType  := lPoset.Iso.Iso.Pack lposet_isoAxiom.

End ClassDef.

Module Export Exports.
Coercion apply : type >-> Funclass.
Coercion  homType : type >-> Hom.type.
Coercion lposet_homType  : type >-> lPoset.Hom.Hom.type.
Coercion lposet_ihomType : type >-> lPoset.iHom.iHom.type.
Coercion lposet_bhomType : type >-> lPoset.bHom.bHom.type.
Coercion lposet_embType  : type >-> lPoset.Emb.Emb.type.
Coercion lposet_isoType  : type >-> lPoset.Iso.Iso.type.
Canonical  homType.
Canonical lposet_homType.
Canonical lposet_ihomType.
Canonical lposet_bhomType.
Canonical lposet_embType.
Canonical lposet_isoType.
End Exports.

End Iso.

Export Iso.Exports.

Module Export Syntax. 
Notation iso := Iso.type.
Notation "{ 'iso' T }" := (@Iso.type_of _ _ _ (Phant T)) : prime_eventstruct_scope.
Notation "[ 'iso' 'of' f ]" := 
  (Iso.mk (fun hCls => @Iso.Pack _ _ _ f hCls))
  (at level 0, format "[ 'iso'  'of'  f ]") : prime_eventstruct_scope.
End Syntax.

Module Export Theory.
Section Theory.
Context {L : Type} {E1 E2 : PrimeC.eventType L} (f : {iso E1 -> E2}).

Lemma wcons_mono : 
  { mono (@!f) : X / wcons X }.
Proof. by case: f=> ? []. Qed.

End Theory.
End Theory.


Module Build.
Section Build.
Context {L : Type} {E E1 E2 E3 : eventType L}.
Implicit Types (f : {iso E2 -> E3}) (g : {iso E1 -> E2}).

Lemma id_axiom : Iso.axiom (@idfun E).
Proof. 
  constructor=> //=; last by exists id. 
  by move=> X; rewrite imfset_id.
Qed.

Lemma comp_axiom f g : Iso.axiom (f \o g).
Proof. 
  apply/Iso.iso_axiom_of.
  - exact/lPoset.Iso.Build.comp_axiom.
  by move=> X /=; rewrite imfset_comp !wcons_mono.
Qed.

End Build.

Module Export Exports.
Section Exports.
Context {L : Type} {E E1 E2 E3 : eventType L}.
Implicit Types (f : {iso E2 -> E3}) (g : {iso E1 -> E2}).

Canonical id_bhom := Iso.Pack (@id_axiom L E).
Canonical comp_bhom f g := Iso.Pack (comp_axiom f g).

End Exports.
End Exports.

End Build.

End Iso.

End PrimeC.

Export PrimeC.EventStruct.Exports.
Export PrimeC.Def.
Export PrimeC.Theory.
Export PrimeC.Syntax.

Export PrimeC.Hom.Hom.Exports.
Export PrimeC.Iso.Iso.Exports.

Export PrimeC.Hom.Build.Exports.
Export PrimeC.Iso.Build.Exports.

Export PrimeC.Hom.Theory.
Export PrimeC.Iso.Theory.


Module Prime.

Module Export EventStruct.
Section ClassDef. 

Record mixin_of (E0 : Type) (L : Type) (b : lPoset.lPoset.class_of E0 L)
                (E := lPoset.lPoset.Pack b) := Mixin {
  (* TODO: better name *)
  bcf : rel E;
  _   : irreflexive bcf;
  _   : symmetric bcf;
  _   : hereditary ca bcf;
}.

Set Primitive Projections.
Record class_of (E L : Type) := Class {
  base   : lPoset.lPoset.class_of E L;
  mixin1 : DwFinPOrder.DwFinPOrder.mixin_of base;
  mixin2 : Countable.mixin_of E;
  mixin3 : Ident.mixin_of (Countable.Class base mixin2);
  mixin4 : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> lPoset.lPoset.class_of.

Local Coercion base2 E L (c : class_of E L) : 
  DwFinPOrder.DwFinPOrder.class_of E := 
    DwFinPOrder.DwFinPOrder.Class (mixin1 c).

Local Coercion base3 E L (c : class_of E L) : 
  Ident.class_of E := Ident.Class (mixin3 c).

Structure type (L : Type) := Pack { sort; _ : class_of sort L }.

Local Coercion sort : type >-> Sortclass.

Variables (E : Type) (L : Type) (cT : type L).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') L in c.
Definition clone c of phant_id class c := @Pack E L c.
(* Definition clone_with disp' c of phant_id class c := @Pack disp' T c. *)

Definition pack :=
  fun bE b & phant_id (@lPoset.lPoset.class L bE) b =>
  fun m1 m2 m3 m4 => Pack (@Class E L b m1 m2 m3 m4).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
(* TODO: countType missing *)
Definition identType := @Ident.Pack cT class.
Definition porderType := @Order.POrder.Pack tt cT class.
Definition dwFinPOrderType := @DwFinPOrder.DwFinPOrder.Pack cT class.
Definition lposetType := @lPoset.lPoset.Pack L cT class.
End ClassDef.

Module Export Exports.
Coercion base : class_of >-> lPoset.lPoset.class_of.
Coercion base2 : class_of >-> DwFinPOrder.DwFinPOrder.class_of.
Coercion mixin1 : class_of >-> DwFinPOrder.DwFinPOrder.mixin_of.
Coercion mixin2 : class_of >-> Countable.mixin_of.
Coercion mixin3 : class_of >-> Ident.mixin_of.
Coercion mixin4 : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion identType  : type >-> Ident.type.
Coercion porderType : type >-> Order.POrder.type.
Coercion dwFinPOrderType : type >-> DwFinPOrder.DwFinPOrder.type.
Coercion lposetType : type >-> lPoset.eventType.
Canonical eqType.
Canonical choiceType.
Canonical identType.
Canonical porderType.
Canonical dwFinPOrderType.
Canonical lposetType.
End Exports.

End EventStruct.

Export EventStruct.Exports.

Notation eventType := EventStruct.type.
Notation eventStruct := EventStruct.class_of.
Notation EventType E L m := (@EventStruct.pack E L _ _ id m).

Module Export Def.
Section Def.

Variable (L : Type) (E : eventType L).

Definition bcf : rel E :=
  EventStruct.bcf (EventStruct.class E).

End Def.
End Def.

Prenex Implicits bcf.

Module Instances.
Section Instances.
Context {L : Type} {E : eventType L}.
Implicit Types (e : E) (X Y : {fset E}).

Definition cons X := 
  ~~ [exists e1 : X, exists e2 : X, bcf (val e1) (val e2)].

Lemma bcf_irr : irreflexive (bcf : rel E).
Proof. by case: E => ? [?] ??? []. Qed.

Lemma bcf_sym : symmetric (bcf : rel E).
Proof. by case: E => ? [?] ??? []. Qed.

Lemma bcf_hered : hereditary ca (bcf : rel E).
Proof. by case: E => ? [?] ??? []. Qed.

Lemma cons_self e : cons [fset e].
Proof.
  apply /fset_exists2P=> [] [] x [] y [].
  by move=> /fset1P -> /fset1P ->; rewrite bcf_irr.
Qed.  

Lemma cons0 : cons fset0.
Proof. by apply/fset_exists2P=>[[>[>[]]]]. Qed.


(* TODO: rename cons_of_contra? *)
Lemma cons_contra (X Y : {fset E}) : X `<=` Y -> cons Y -> cons X.
Proof.
  move=> sub /= /fset_exists2P nCF. 
  apply/fset_exists2P=> [[]] x [] y [].
  move=> /(fsubsetP sub) ? /(fsubsetP sub) ??.
  by apply /nCF; exists x, y.
Qed.

Lemma cons_prop (X : {fset E}) (e1 e2 : E) :
  e1 <= e2 -> cons (e2 |` X) -> cons (e1 |` X).
Proof.
  move => ca12 /fset_exists2P ncf.
  apply/fset_exists2P=> [[]] e3 [] e4 [].
  rewrite !inE=> /orP [/eqP->|/[swap]]/orP[/eqP->|].
  - by rewrite bcf_irr.
  - move=> inX cf14; apply/ncf. 
    exists e4, e2; rewrite !inE; split.
    + by apply/orP; right.
    + by apply/orP; left.
    by apply/(bcf_hered _ ca12); rewrite bcf_sym.
  - move=> inX cf31; apply/ncf. 
    exists e3, e2; rewrite !inE; split.
    + by apply/orP; right.
    + by apply/orP; left.
    by apply/(bcf_hered _ ca12).
  move=> ???; apply/ncf. 
  exists e3, e4; rewrite !inE. 
  by split=> //; apply/orP; right.
Qed.

Definition primeCMixin := 
  PrimeC.EventStruct.Mixin 
    cons0 
    cons_self 
    cons_contra
    cons_prop.

Definition primeCeventType := 
  PrimeC.EventStruct.Pack 
  (PrimeC.EventStruct.Class (class E) (mixin3 (class E)) primeCMixin).

End Instances.

Module Export Exports.
Coercion primeCeventType : type >-> PrimeC.EventStruct.type.
Canonical primeCeventType.
End Exports.

End Instances.

Export Instances.Exports.

Module Export Theory.
Section Theory.
Context {L : Type} {E : eventType L}.
Implicit Types (e : E) (X Y : {fset E}).

Lemma bcfE : 
  (bcf : rel E) =2 cf. 
Proof. 
  rewrite /cf /gcf /cons /= => e1 e2 /=.
  rewrite negbK; apply/idP/idP.
  - move=> ?; apply/fset_exists2P.
    by exists e1, e2; rewrite !inE !eq_refl orbT; split=> //.
  move=> /fset_exists2P[] e [] e' [].
  rewrite !inE=> /orP[/eqP->|/eqP->] /orP[/eqP->|/eqP->] //; 
    try by rewrite Instances.bcf_irr.
  by rewrite Instances.bcf_sym.
Qed.

Lemma bgcfP X : 
  reflect (exists e1 e2, [/\ e1 \in X, e2 \in X & cf e1 e2]) (gcf X).
Proof. 
  apply/(equivP idP); split; last first.
  - move=> [e1] [e2] []; exact/cf_gcf.
  rewrite /gcf /cons /=.
  rewrite negbK=> /fset_exists2P [] e1 [] e2 [].
  by rewrite bcfE=> ???; exists e1, e2.
Qed.

Lemma bgcfE X : 
  gcf X = [exists e1 : X, exists e2 : X, cf (val e1) (val e2)].
Proof. apply/(sameP (bgcfP X)); exact/fset_exists2P. Qed.
   
End Theory.
End Theory.

End Prime.

Export Prime.EventStruct.Exports.
Export Prime.Instances.Exports.
Export Prime.Theory.

(* Section Test. *)

(* Context {L : Type} {E : Prime.eventType L}. *)
(* Variable (e1 e2 : E) (s : {fset E}). *)

(* Check (e1 <= e2 : bool). *)
(* Check (e1 \# e2 : bool). *)
(* Check (PrimeG.gcf s : bool). *)

(* End Test. *)
