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
  _ : forall (e : E), cons [fset e];
  _ : forall (X Y : {fset E}), X `<=` Y -> cons Y -> cons X;
  _ : forall X e e', e <= e' -> cons (e' |` X) -> cons (e |` X)
}.

Set Primitive Projections.
Record class_of (E L : Type) := Class {
  (* TODO: inherit DwFinPOrder in lPoset.class_of ? *)
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
  ca_closed p /\ cf_free p.

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

Lemma prefix_ca_closed (e : E) : ca_closed (<= e).
Proof. move=> e1 e2 /=; exact: le_trans. Qed.

Lemma prefix_cf_free e : cf_free (<= e).
Proof. 
  move=> X S; apply/(@cons_ca_contra _ [fset e])/cons_self.
  move=> x i; exists e; rewrite ?inE //; exact/S.
Qed.

Lemma prefix_cfg e : cfg (<= e).
Proof. split; [exact/prefix_ca_closed | exact/prefix_cf_free]. Qed.

Lemma cf_free_fset (X : {fset E}) : reflect (cf_free (mem X)) (cons X).
Proof.
  apply/(iffP idP)=> [?? /fsubsetP/cons_contra|]; exact.
Qed.

Lemma cfg0 : cfg (mem (fset0 : {fset E})).
Proof.
  split=> [> /=|]; first by rewrite inE.
  apply/cf_free_fset/cons0.
Qed.

End Theory.
End Theory.

Section Lang.
Context {L : choiceType} (bot : L).

Section Build.
Context {E : eventType L}.
Implicit Types (e : E) (X Y : {fset E}).

Context (X : {fset E}).
Hypothesis lab_def : [forall x : X, lab (val x) != bot].

Definition lfspreposet_of := 
  @lFsPrePoset.build E L bot X (lab \o val) (cov (relpre val sca)).

Lemma lfspreposet_of_finsupp : 
  finsupp lfspreposet_of = X.
Proof. exact/lFsPrePoset.build_finsupp/forallP. Qed.

Lemma connect_ca (Y : {fset E}): 
  (connect (relpre val ca) : rel Y) =2 relpre val ca.
Proof.
  move=>>; apply/(sameP idP)/(equivP idP); split=> [/connect1 //|].
  apply/sub_connectP/rtclosedP; split; move=>>.
  - exact/lexx.
  exact/le_trans.
Qed.

(* TODO: generalize? *)
Lemma lfsposet_of_fin_ca : 
  fin_ica lfspreposet_of =2 cov (relpre val sca).
Proof.
  case=> ? /[dup] + in1 [? /[dup] + in2]; rewrite {1 2}lfspreposet_of_finsupp=> *.
  rewrite /fin_ica /sub_rel_down /=.
  rewrite lFsPrePoset.build_ica /sub_rel_lift /=.
  do ? case: insubP=> [??? |/negP//].
  move: in1 in2; case: _ / (esym lfspreposet_of_finsupp)=> *.
  apply/congr2/val_inj=> //; exact/val_inj.
Qed.

Lemma connect_sca (Y : {fset E}): 
  (connect (relpre val sca) : rel Y) =2 connect (relpre val ca).
Proof.
  move=>>; rewrite ?(connect_sub_one (relpre val ca)).
  - apply eq_connect=> [[/= ?? [?? /=]]]; rewrite /sca lt_def. 
  by rewrite -(inj_eq val_inj) /= eq_sym /ca.
Qed.

Lemma lfspreposet_of_connect_fin_ca : 
  connect (fin_ica lfspreposet_of) =2 relpre val ca.
Proof.
  move=> x y; under eq_connect do rewrite lfsposet_of_fin_ca.
  rewrite -connect_ca connect_covE ?connect_sca //. 
  apply/acyclicP; split=> [[/= ??]|]; first by rewrite /sca ltxx.
  apply/preacyclicP=> [][??][??] /andP[]; rewrite ?connect_sca ?connect_ca.
  by move=> /=*; apply/val_inj/(@le_anti tt)/andP.
Qed.

Lemma lfspreposet_of_mixin :
  [&& lab_defined lfspreposet_of,
      supp_closed lfspreposet_of &
      acyclic (fin_ica lfspreposet_of)].
Proof.
  apply/and3P; split.
  - apply/lab_definedP=>>. 
    rewrite lFsPrePoset.build_lab lfspreposet_of_finsupp /sub_lift.
    case: insubP=> [/= + _ _ _ |/negP//]; exact/forallP.
  - apply/supp_closedP=>>.
    rewrite lFsPrePoset.build_ica /sub_rel_lift /=.
    do ? case: insubP=> // ??; by rewrite lfspreposet_of_finsupp.
  apply/acyclicP; split=> [[?]|].
  - rewrite /fin_ica /sub_rel_down /= lFsPrePoset.build_ica.
    rewrite lfspreposet_of_finsupp /sub_rel_lift /==> T.
    by rewrite insubT /cov /= eqxx.
  apply/preacyclicP=>> /andP[]; rewrite ?lfspreposet_of_connect_fin_ca=> *.
  exact/val_inj/(@le_anti tt)/andP. 
Qed.

End Build.

Definition lfsposet_of (E : eventType L) (X : {fset E}) : lfsposet E L bot :=
  if eqP is ReflectT p then
    lFsPoset (@lfspreposet_of_mixin E X p)
  else (lFsPoset.empty E L bot).

Section lFsPoset_of.
Context (E : eventType L) (X : {fset E}).

Lemma lfsposet_of0 : 
  lfsposet_of (fset0 : {fset E}) = lFsPoset.empty E L bot.
Proof.
  rewrite /lfsposet_of /lfspreposet_of; case: eqP=> // ?.
  apply/eqP/lfsposet_eqP; split=>>; rewrite /lFsPoset.empty /=.
  - rewrite lFsPrePoset.fs_lab_empty lFsPrePoset.build_lab /sub_lift.
    by case: insubP.
  rewrite lFsPrePoset.fs_ica_empty lFsPrePoset.build_ica /sub_rel_lift /=.
  by case: insubP.
Qed.

Lemma lfsposet_of_emp : 
  [forall x : X, lab (val x) != bot] <> true ->
  lfsposet_of X = (lFsPoset.empty E L bot).
Proof. by rewrite /lfsposet_of; case: eqP. Qed.

Hypothesis lab_def : [forall x : X, lab (val x) != bot].

Lemma lfsposet_of_finsupp : 
  finsupp (lfsposet_of X) = X.
Proof.
  rewrite /lfsposet_of; case: eqP=> // *.
  exact/lfspreposet_of_finsupp.
Qed.

Lemma lfsposet_of_lab :
  {in X, fs_lab (lfsposet_of X) =1 lab}.
Proof.
  rewrite /lfsposet_of; case: eqP=> //= ? ?.
  rewrite /lfspreposet_of /= lFsPrePoset.build_lab /sub_lift.
  by case: insubP=> //= [??->|/negP].
Qed.

Lemma connect_fin_ca : 
  connect (fin_ica (lfsposet_of X)) =2 relpre val ca.
Proof.
  rewrite /lfsposet_of; case: eqP=> //= ?>.
  by rewrite lfspreposet_of_connect_fin_ca.
Qed.

End lFsPoset_of.

Lemma lfsposet_of0_finsupp (E : eventType L): 
  finsupp (lfsposet_of (fset0 : {fset E})) = fset0.
Proof. apply/lfsposet_of_finsupp/forallP; by case. Qed.

Definition pomset_lang (E : eventType L) := fun (p : pomset E L bot) =>
  exists2 X : {fset E}, cfg (mem X) & p = \pi (lfsposet_of X).

End Lang.

Module Export Hom.

Module Hom.
Section ClassDef. 

(* TODO: homomorphism between pomsets labelled by different labels? *)
Context {L : Type} (E1 E2 : PrimeC.eventType L).
Implicit Types (f : E1 -> E2).

Record mixin_of f := Mixin {
  _ : forall e, lab (f e) = lab e;
  _ : forall e1 e2, e1 <= f e2 -> exists2 e, e1 = f e & e <= e2;
  _ : forall X : {fset E1}, wcons X -> wcons (f @` X)
}.

Set Primitive Projections.
Record class_of f := Class {
  mixin : mixin_of f;
}.
Unset Primitive Projections.

Structure type := Pack { apply ; _ : class_of apply }.

Local Coercion apply : type >-> Funclass.

Variables (cT : type).

Definition class := let: Pack _ c as cT' := cT return class_of (apply cT') in c.
Definition clone f c of phant_id class c := @Pack f c.


Definition mk h mkH : type :=
  mkH (let: Pack _ c := h return @class_of h in c).

Definition type_of (_ : phant (E1 -> E2)) := type.

(* Definition pack := *)
(*   fun bE b & phant_id (@Order.POrder.class tt bE) b => *)
(*   fun m => Pack (@Class E L b m). *)

End ClassDef.

Module Export Exports.
Coercion mixin : class_of >-> mixin_of.
Coercion apply : type >-> Funclass.
End Exports.

End Hom.

Export Hom.Exports.

Module Export Syntax. 
Notation hom := Hom.type.
Notation "{ 'hom' T }" := (@Hom.type_of _ _ _ (Phant T)) : prime_eventstruct_scope.
Notation "[ 'hom' 'of' f ]" := 
  (Hom.mk (fun hCls => @Hom.Pack _ _ _ f hCls))
  (at level 0, format "[ 'hom'  'of'  f ]") : prime_eventstruct_scope.
End Syntax. 

Module Export Theory.
Section Theory. 
Context {L : choiceType} {E1 E2 : eventType L} (f : {hom E1 -> E2}) (bot : L).

Lemma wcons_mon (X : {fset E1}) : 
  wcons X -> wcons (f @` X).
Proof. case: f=> ? [[??+?]]; exact. Qed.

Lemma lab_preserving :
  { mono f : e / lab e }.
Proof. by case: f => ? [[]]. Qed.

Lemma cons_mon (X : {fset E1}): 
  cons X -> cons (f @` X).
Proof.
  move=> c; case: (boolP (wcons X))=> [/wcons_mon/andP[]|] //.
  rewrite /wcons /= negb_and c /= negbK=>/cardfs1P[?->].
  by rewrite imfset1 cons_self.
Qed.

Lemma gcf_mon (X : {fset E1}) (e : E2) : 
  gcf (f @` X) -> gcf X.
Proof. exact/contra/cons_mon. Qed.

Lemma cf_mon e1 e2 :
  cf (f e1) (f e2) -> cf e1 e2.
Proof. 
  rewrite /cf=> ?; apply/(gcf_mon (f e1)).
  by rewrite imfsetU !imfset1=> /=.
Qed.

Lemma hom_prefix e1 e2 : e1 <= f e2 -> exists2 e, e1 = f e & e <= e2.
Proof. case: f=> ? [[/= ?+?]]; exact. Qed.

Lemma hom_cons_inj X : cons X -> {in X & X, injective f}.
Proof.
  move=> c e1 e2 ??.
  case: (boolP (wcons [fset e1; e2]))=> [/wcons_mon/[swap] Ef|].
  - by rewrite imfsetU ?imfset1 /wcons /= cardfs2 Ef eqxx /= andbF.
  rewrite /wcons /= negb_and negbK cardfs2.
  case: (e1 =P e2)=> //= ? /orP[]// /negP[].
  by apply/(cons_contra _ c)/fsubsetP=>>; rewrite ?inE=>/orP[]/eqP->.
Qed.

Lemma in_cons_ca_anti X :
  cons X ->
  {in X & X, forall e1 e2, ca (f e1) (f e2) -> ca e1 e2}.
Proof.
  move=> c e1 e2 i ? /hom_prefix[x /[swap] l /(@hom_cons_inj (x |` X))-> //].
  - by apply/(cons_prop l); rewrite mem_fset1U.
  all: by rewrite ?inE (i, eqxx).
Qed.


Lemma pomset_lang_sub (p : pomset E1 L bot) :
  (forall x : E2, lab x != bot) ->
  pomset_lang p -> 
  exists2 q : pomset E2 L bot, pomset_lang q & bhom_le q p.
Proof.
  move=> ld2 [X [ccX cfX]].
  case: ([forall x : X, lab (val x) != bot] =P true); first last.
  - move/lfsposet_of_emp=>->->.
    exists (\pi (lFsPoset.empty E2 L bot)).
    + exists fset0; first exact/cfg0; by rewrite lfsposet_of0.
    rewrite pi_bhom_le -?lfsposet_of0; apply/lFinPoset.fbhomP.
    (* have g: forall E E' : eventType L, *)
    (*         [FinEvent of @lfsposet_of L bot E  fset0] -> *)
    (*         [FinEvent of @lfsposet_of L bot E' fset0]. *)
    have g: forall E E' : eventType L,
            (finsupp (lfsposet_of bot (fset0 : {fset E}))) ->
            (finsupp (lfsposet_of bot (fset0 : {fset E'}))) .
    + by move=> ??; rewrite ?lfsposet_of0_finsupp=> [[]].
    exists=> /=. exists (g E2 E1). do ? split=> /=.
    1,2: by move=> /[dup]; rewrite {1}lfsposet_of0_finsupp=> [[]].
    by exists (g E1 E2)=> /[dup] /=; rewrite {1}lfsposet_of0_finsupp=> [[]].
  move=> ld1 pE; exists (\pi (lfsposet_of bot (f @` X))).
  - exists (f @` X)=> //; split; last exact/cf_free_fset/cons_mon/cfX.
    move=>> /[swap]/imfsetP[] /= x' /[swap]-> /[swap] /hom_prefix.
    case=> y' -> /ccX/[apply] ?; by apply/imfsetP; exists y'.
  rewrite pE pi_bhom_le.
  have ?: [forall x : (f @` X), lab (val x) != bot] by exact/forallP.
  have In: forall x : (finsupp (lfsposet_of bot X)),
    f (val x) \in (finsupp (lfsposet_of bot (f @` X))).
  - case=> /= x; rewrite ?lfsposet_of_finsupp //. 
    move=> ?; by rewrite in_imfset.
  set g : 
    [FinEvent of lfsposet_of bot X] -> 
    [FinEvent of lfsposet_of bot (f @` X)] := fun x => [` (In x)].
  apply/lFinPoset.fbhomP/(@lPoset.bHom.Build.of_anti_bhom_ex _ _ _ g)=> /=.
  - apply/inj_card_bij=> /=.
    rewrite /g; case=> ? in1 [? in2 /=] /(congr1 val) /= /hom_cons_inj.
    move/(_ _ _ in1 in2)=> ev; apply/val_inj/ev/cfX=> ?.
    by rewrite lfsposet_of_finsupp.
  - rewrite ?lfsposet_of_finsupp // -?cardfE.
    exact/(leq_trans (leq_imfset_card _ _ _)).
  - case=> /= ? /[dup]; rewrite {1}lfsposet_of_finsupp // => ?.
    rewrite /g /lab /= /fin_lab /= ?lfsposet_of_lab ?lab_preserving //.
    by rewrite ?in_imfset //.
  case=> ? /[dup] + ? [? /[dup]+?]; rewrite {1 2}lfsposet_of_finsupp // => ??.
  rewrite /g ?/(_ <= _) /= /fin_ca /=.
  rewrite ?connect_fin_ca // /==> /(@in_cons_ca_anti X); apply=> //.
  exact/cfX.
Qed.

End Theory.
End Theory.

Module Build.
Section Build.
Context {L : choiceType}.
Implicit Types (E : eventType L).

Definition mk_hom {E1 E2 : eventType L} h mkH : {hom E1 -> E2} :=
  mkH (let: Hom.Pack _ c := h return @Hom.class_of L E1 E2 h in c).

Lemma id_class {E} : Hom.class_of (@idfun E).
Proof.
  (do 2 split)=> //= e; rewrite ?imfset_id //.
  by exists e. 
Qed.

Lemma comp_class {E1 E2 E3} (f : {hom E2 -> E3}) (g : {hom E1 -> E2}) : 
  Hom.class_of (comp f g).
Proof. 
  (do 2 split)=> /= >.
  - by rewrite ?lab_preserving.
  - case/hom_prefix=> ?-> /hom_prefix[e->]; by exists e.
  by rewrite imfset_comp=> *; do 2 apply/wcons_mon.
Qed.

Lemma of_eqfun_class {E1 E2} (f : {hom E1 -> E2}) g : 
  g =1 f -> Hom.class_of g.
Proof. 
  move=> H; (do 2 split); move=>>.
  - rewrite !H; exact/lab_preserving.
  - move=> /[!H]/hom_prefix[e]/[-!H]; by exists e.
  move/(wcons_mon f); by under eq_imfset do [rewrite -H|by[]].
Qed.

Definition of_eqfun {E1 E2} (f : {hom E1 -> E2}) g : g =1 f -> {hom E1 -> E2} := 
  fun eqf => Hom.Pack (of_eqfun_class eqf).

End Build.

Module Export Exports.
Section Exports.
Context {L : choiceType}.
Implicit Types (E : eventType L).

Canonical id_hom E : {hom E -> E} := Hom.Pack id_class.

Canonical comp_hom E1 E2 E3 : {hom E2 -> E3} -> {hom E1 -> E2} -> {hom E1 -> E3} :=
  fun f g => Hom.Pack (comp_class f g).

End Exports.
End Exports.
End Build.

End Hom.

Module Export Iso.

Module Iso.
Section ClassDef. 

Context {L : Type} (E1 E2 : PrimeC.eventType L).
Implicit Types (f : E1 -> E2).

Record mixin_of f := Mixin {
  _ : forall X : {fset E1}, cons X <-> cons (f @` X)
}.

Set Primitive Projections.
Record class_of f := Class {
  base  : lPoset.Iso.Iso.class_of f;
  mixin : mixin_of f
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> lPoset.Iso.Iso.class_of.

Structure type := Pack { apply ; _ : class_of apply }.

Local Coercion apply : type >-> Funclass.

Variables (cT : type).

Definition class := let: Pack _ c as cT' := cT return class_of (apply cT') in c.
Definition clone f c of phant_id class c := @Pack f c.

(* Definition pack := *)
(*   fun bE b & phant_id (@Order.POrder.class tt bE) b => *)
(*   fun m => Pack (@Class E L b m). *)

Definition lposetIsoType  := lPoset.Iso.Iso.Pack class.
Definition lposetHomType := lPoset.Hom.Hom.Pack class.
Definition lposetbHomType := lPoset.bHom.bHom.Pack class.  

Lemma hom_class_of : Hom.class_of cT.
Proof.
  case: cT=> f [/= [[[[/= lp cm [g c1 c2 [cam [ce]]]]]]]].
  do ? split=> //.
  - move=> e1 ?; exists (g e1)=> //; apply/cam; by rewrite c2.
  - move=> X /andP[/ce ??]; apply/andP; split=> //.
    rewrite card_in_imfset=> //>??; exact/(can_inj c1).
Qed.

Definition homType := Hom.Pack hom_class_of.

Definition mk h mkH : type :=
  mkH (let: Pack _ c := h return @class_of h in c).

Definition type_of (_ : phant (E1 -> E2)) := type.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> lPoset.Iso.Iso.class_of.
Coercion apply : type >-> Funclass.
Coercion homType  : type >-> Hom.type.
Coercion lposetIsoType : type >-> lPoset.Iso.Iso.type.
Coercion lposetHomType : type >-> lPoset.Hom.Hom.type.
Coercion lposetbHomType : type >-> lPoset.bHom.bHom.type.
Canonical homType.
Canonical lposetHomType.
Canonical lposetbHomType.
Canonical lposetIsoType.
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

Lemma cons_fE (X : {fset E1}) : cons X <-> cons (f @` X).
Proof. by case: f=> ? [? []]. Qed.

End Theory.
End Theory.


Module Build.
Section Build.
Context {L : Type}.
Implicit Types (E : eventType L).

Lemma id_class {E} : Iso.class_of (@idfun E).
Proof.
  split; first exact/lPoset.Iso.Build.id_class.
  by split=> ?; rewrite imfset_id. 
Qed.

Lemma inv_class {E1 E2} (f : {iso E1 -> E2}) :
  Iso.class_of (lPoset.bHom.invF f).
Proof.
  case: (lPoset.Iso.Build.inv_class [iso of f]%pomset)=> [[[[??[g ??[?]]]]]].
  do ? split=> //; [by exists g| |].
  - move=> ?; rewrite (cons_fE f) -imfset_comp.
    by under eq_imfset do [rewrite /= can_inv|by []]; rewrite imfset_id.
  move/(cons_fE f); rewrite -imfset_comp.
  by under eq_imfset do [rewrite /= can_inv|by []]; rewrite imfset_id.
Qed.

Lemma comp_class {E1 E2 E3} (f : {iso E2 -> E3}) (g : {iso E1 -> E2}) : 
  Iso.class_of (f \o g).
Proof.
  split; first exact/lPoset.Iso.Build.comp_class.
  by split=> X; rewrite imfset_comp -?cons_fE.
Qed.

Lemma of_eqfun_class {E1 E2} (f : {iso  E1 -> E2}) g :
  g =1 f -> Iso.class_of g.
Proof.
  move=> E; split; first exact/(lPoset.Iso.Build.of_eqfun_class E).
  split; move=> ?; under eq_imfset do [rewrite E|by []]; exact/cons_fE.
Qed.

Definition of_eqfun {E1 E2} (f : {iso  E1 -> E2}) g : g =1 f -> {iso  E1 -> E2} := 
  fun eqf => Iso.Pack (of_eqfun_class eqf).

End Build.
Module Export Exports.
Section Exports.
Context {L : Type}.
Implicit Types (E : eventType L).

Canonical id_iso E : {iso E -> E} := Iso.Pack id_class.

Canonical comp_iso E1 E2 E3 : {iso E2 -> E3} -> {iso E1 -> E2} -> {iso E1 -> E3} :=
  fun f g => Iso.Pack (comp_class f g).

Canonical inv {E1 E2} : {iso E1 -> E2} -> {iso E2 -> E1} := 
  fun f => Iso.Pack (inv_class f).

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
