From Coq Require Import Relations.
From RelationAlgebra Require Import lattice monoid rel boolean kat_tac.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat seq tuple.
From mathcomp Require Import eqtype choice order generic_quotient.
From mathcomp Require Import fintype finfun finset fingraph finmap zify.
From mathcomp.tarjan Require Import extra acyclic kosaraju acyclic_tsorted. 
From eventstruct Require Import utils rel relalg inhtype ident lts lposet.

(******************************************************************************)
(* This file contains theory of finitely supported labelled posets,           *)
(* pomsets represented as their quotients, and pomset languages, i.e.         *)
(* propositional predicates over pomsets.                                     *)
(* Finitely supported lposet is encoded as a finitely supported function      *)
(* from event to its label and a sequence of its immediate predecessors.      *)
(*                                                                            *)
(*      lfspreposet E L bot == finitelly supported labelled pre-poset over    *)
(*                             type of events E and type of labels L.         *)
(*                          := { fsfun E -> (L * seq E) of e => (bot, [::]) } *)
(*                             s.t. given an event e in support,              *)
(*                             f(e) == (l, es), where l is label of e and     *)
(*                             es are immediate predecessors of e.            *)
(*                             Outside of the support, f(e) == (bot, [::]),   *)
(*                             where bot is some default label.               *) 
(*         lfsposet E L bot == finitelly supported labelled poset.            *)
(*                             It is a preposet satisfying additionally that: *)
(*                               (1) all predecessors of each event belong    *)
(*                                   to the support of poset;                 *)
(*                               (2) causality relation is partial order.     *)
(*                             lfsposet is a subType of lfspreposet and thus  *)
(*                             coerces to it. Moreover, both types have       *)
(*                             instances of eqType and choiceType.            *)
(*           pomset E L bot == pomset - a class of isomorphic finitely        *)
(*                             supported lposets, defined as a quotient type  *)
(*                             over finitely supported lposets by             *)
(*                             isomorphism relation.                          *)
(*    fs_(lab|ica|ca|sca) p == labelling function, immediate causality,       *)
(*                             causality and strict causality relations of    *)
(*                             the preposet/poset/pomset p.                   *) 
(*   fin_(lab|ica|ca|sca) p == same functions/relations but defined on        *)
(*                             the finite type of support of the p.           *)
(*                                                                            *)  
(* Given a lfsposet (or pomset) one can obtain the induced lPoset structure   *)  
(* using the following notations.                                             *)  
(*             [Event of p] == lPoset.eventType structure induced by p.       *)
(*                             The type of the events are the same as of p.   *) 
(*          [FinEvent of p] == lFinPoset.eventType structure induced by p.    *)
(*                             The type of the events are of the finite       *)
(*                             support of p.                                  *)
(*                                                                            *)  
(******************************************************************************)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.LTheory.

Local Open Scope order_scope.
Local Open Scope fset_scope.
Local Open Scope quotient_scope.
Local Open Scope ra_terms.
Local Open Scope ident_scope.
Local Open Scope lposet_scope.

Declare Scope pomset_scope.
Delimit Scope pomset_scope with pomset.

Local Open Scope pomset_scope.


(* Notation lfspreposet E L bot :=  *)
(*   ({ fsfun E -> (L * {fset E}) of e => (bot, fset0) }). *)

Module lFsPrePoset. 

Module Export Def.
Section Def.
(* TODO: perhaps, it is better to make L : inhType *)
Context (E : identType) (L : eqType) (bot : L).

(* TODO: perhaps, we should actually enforce 
 *   lab_defined and supp_closed properties here
 *)
Definition lfspreposet := 
  { fsfun E -> (L * {fset E}) of e => (bot, fset0) }.

(* TODO: maybe get rid of this coercion? *)
Identity Coercion lfspreposet_to_fsfun : lfspreposet >-> fsfun. 

Implicit Types (p : lfspreposet).
Implicit Types (es : {fset E}).

Definition fs_lab p : E -> L := 
  fun e => (p e).1. 

Definition fin_lab p : finsupp p -> L := 
  fun e => fs_lab p (val e).

Definition fs_rcov p : E -> {fset E} := 
  fun e => (p e).2. 

Definition fs_ica p : rel E := 
  [rel x y | grel (fs_rcov p) y x]. 

Definition fin_ica p : rel (finsupp p) := 
  sub_rel_down (fs_ica p).

Definition fin_ca p : rel (finsupp p) := 
  connect (@fin_ica p).

Definition fin_sca p : rel (finsupp p) := 
  fun e1 e2 => (e2 != e1) && (@fin_ca p e1 e2).

Definition fs_ca p : rel E := 
  (sub_rel_lift (@fin_ca p) : {dhrel E & E})^?.

Definition fs_sca p : rel E := 
  fun e1 e2 => (e2 != e1) && (fs_ca p e1 e2).

Definition lab_defined p := 
  [forall e : finsupp p, fs_lab p (val e) != bot].

Definition supp_closed p := 
  [forall e : finsupp p, fs_rcov p (val e) `<=` finsupp p].

(* TODO: better name? *)
Definition operational p := 
  [forall e1 : finsupp p, forall e2 : finsupp p, 
    (fs_ca p (val e1) (val e2)) ==> (val e1 <=^i val e2)
  ].

Definition lfsp_tseq p : seq E := 
  map val (tseq (rgraph (@fin_ica p))).

Definition lfsp_idx p : E -> nat := 
  fun e => index e (lfsp_tseq p). 

Definition lfsp_event p e0 : nat -> E := 
  fun n => nth e0 (lfsp_tseq p) n.

Definition lfsp_labels p : seq L := 
  map (fs_lab p) (lfsp_tseq p).

Definition lfsp_fresh p : E := 
  fresh_seq (finsupp p).

(* TODO: unify with UpFinPOrder *)
Definition lfsp_dw_clos p es := 
  [seq e <- finsupp p | [exists e' : es, fs_ca p e (val e')]].

End Def.

Arguments fs_lab {E L bot} p.
Arguments fs_ica {E L bot} p.
Arguments fs_sca {E L bot} p.
Arguments fs_ca  {E L bot} p.

Arguments fin_lab {E L bot} p.
Arguments fin_ica {E L bot} p.
Arguments fin_sca {E L bot} p.
Arguments fin_ca  {E L bot} p.

End Def.

Arguments lfspreposet E L bot : clear implicits.

Module Export Theory.
Section Theory.
Context (E : identType) (L : eqType).
Variable (bot : L).
Implicit Types (p : lfspreposet E L bot) (ls : seq L).

Lemma lab_definedP p : 
  reflect {in finsupp p, forall e, fs_lab p e != bot} (lab_defined p).
Proof. 
  rewrite /lab_defined /fs_lab. 
  apply/equivP; first exact/forallP.
  split=> H e /=.
  - case: finsuppP=> //= inP _.
    by rewrite (H (Sub e inP)).
  by rewrite (H (val e) (valP e)).
Qed.

Lemma supp_closedP p : 
  reflect (forall e1 e2, fs_ica p e1 e2 -> 
            (e1 \in finsupp p) * (e2 \in finsupp p))
          (supp_closed p).
Proof. 
  rewrite /supp_closed /fs_ica /fs_rcov. 
  apply/(equivP forallP); split=> /=; last first.
  - move=> ica_supp; case=> e2 in_supp /=. 
    by apply/fsubsetP=> e1 /ica_supp [].
  move=> all_supp e1 e2 /=.
  case: (in_fsetP (finsupp p) e2)=> [e2'|].
  - by move: (all_supp e2')=> /fsubsetP /[swap] /= <- /[apply] ->.
  by move=> /fsfun_dflt -> //.
Qed.

Lemma fs_caP p e1 e2 : supp_closed p -> 
  reflect (clos_refl_trans (fs_ica p) e1 e2) (fs_ca p e1 e2).
Proof. 
  (* TODO: try to simplify proof *)
  move=> supcl; apply/equivP.  
  - apply/(equivP idP); apply: iff_trans.
    - by apply/rel_qmk_m.
    rewrite qmk_weq; last first.
    - move=> /= x y; rewrite /fs_ca.
      apply: iff_sym; apply: rwP.
      apply/sub_rel_liftP. 
    by apply: iff_refl. 
  apply: iff_trans=> /=. 
  - apply: or_iff_compat_l.
    apply/exists_equiv=> e1'.
    apply/exists_equiv=> e2'.
    (* TODO: make lemma? *)
    have H: forall A1 A2 B C, A1 <-> A2 -> [/\ A1, B & C] <-> [/\ A2, B & C].
    - move=> ???? [H1 H2]; split; move=> [???]; split=> //; [exact/H1|exact/H2].
    apply/H; apply: iff_sym. 
    apply: iff_trans; last first. 
    - apply: rwP; exact/(connect_strP).
    by apply/clos_rt_str.
  (* apply: iff_trans; last first. *)
  (* - by apply/clos_rt_str. *)
  move=> /=; split=> [[|[e1' [] e2' []]] |].
  - move=> ->; exact/rt_refl.
  - move=> + <- <-; elim=> //.
    + move=> ??; exact/rt_step.
    move=> ??? ? + ?; exact/rt_trans.
  elim=> //=.
  - move=> {}e1 {}e2 /[dup] /(supp_closedP _ supcl)[].
    move=> Pe1 Pe2 ica; right; exists (Sub e1 Pe1), (Sub e2 Pe2).
    by split=> //; apply/rt_step.
  - by move=> ?; left.
  move=> ??? ? [-> ? [->|] | + ? [|]]. 
  - by left.
  - move=> [e1' [] e2' []] ???.
    by right; exists e1', e2'.
  - move=> [e1' [] e2' []] ??? <-.
    by right; exists e1', e2'.
  move=> [e1' [] e2' []] rt12 ??.
  move=> [e3' [] e4' []] rt34 ??.
  right; exists e1', e4'; split=> //=.
  apply/rt_trans; first exact/rt12. 
  suff: e2' = e3'=> [->|] //.
  apply/val_inj=> /=; congruence.
Qed.  

Lemma fs_ca_scaE p e1 e2 : 
  fs_ca p e1 e2 = (e1 == e2) || (fs_sca p e1 e2).
Proof.
  rewrite /fs_sca orb_andr eq_sym orbN andTb. 
  apply/esym; rewrite orb_idl //.
  move=> /eqP->; rewrite /fs_ca /=. 
  by apply/orP; left.
Qed.

Lemma fs_ica_ct_fin_sca p : supp_closed p -> acyclic (fin_ica p) ->
  clos_trans (fs_ica p) ≦ sub_rel_lift (fin_sca p).
Proof. 
  move=> supcl acyc e1 e2; elim; clear e1 e2.
  - move=> x y; rewrite /sub_rel_lift /=.
    move=> /[dup] /(supp_closedP _ supcl) [xIn yIn].
    rewrite !insubT /fin_sca /fin_ca /fin_ica=> ica_xy.
    have: fin_ica p (Sub x xIn) (Sub y yIn).    
    - by rewrite /fin_ica /sub_rel_down /=.
    move=> fica_xy; apply/andP; split; last first.
    - by apply/connect1. 
    move: (acyc_irrefl acyc)=> irr. 
    apply/eqP=> eq_xy. 
    move: fica_xy; rewrite eq_xy.
    by move: (irr (Sub x xIn))=> ->.
  move=> x y z ? H1 ? H2.  
  apply/sub_rel_lift_trans; last first.
  - exact/H2.
  - exact/H1.
  move=> z' x' y'; rewrite /fin_sca /fin_ca. 
  move=> /andP[/eqP neq_zx Hxz] /andP[/eqP neq_yz Hzy]. 
  apply/andP; split; last first.
  - apply/connect_trans; [exact/Hxz | exact/Hzy].
  apply/eqP=> eq_xy. 
  move: eq_xy Hxz Hzy=> -> ??.
  suff: x' = z'. 
  - by move: neq_zx=> /[swap]->.
  move: acyc=> /acyc_antisym antisym.
  by apply/antisym/andP.  
Qed.

(* TODO: maybe prove for lfsposet? *)
Lemma fs_scaP p e1 e2 : supp_closed p -> acyclic (fin_ica p) ->
  reflect (clos_trans (fs_ica p) e1 e2) (fs_sca p e1 e2).
Proof. 
  move=> supcl acyc.
  apply/equivP; last first.
  - symmetry; apply/clos_t_itr.
  suff: (fs_ica p : hrel E E)^+ ≡ !1 ⊓ (fs_ca p : hrel E E).
  - move=> scaE.
    apply/equivP; last first.
    + symmetry; apply/scaE.
    rewrite /fs_sca eq_sym.
    apply/(equivP idP); split.
    + by move=> /andP[] /eqP. 
    by move=> /= [/eqP ??]; apply/andP.
  rewrite -capC. 
  have->: (fs_ica p : hrel E E)^+ ≡ (fs_ica p : hrel E E)^+ \ 1.
  - apply/weq_spec; split; last by lattice.
    rewrite -clos_t_itr; move=> x y /= ica_xy; split=> //.
    move: ica_xy=> /[swap] <-.
    move=> /(fs_ica_ct_fin_sca supcl acyc).
    rewrite /sub_rel_lift /=.            
    case: insubP=> // x'.
    by rewrite /fin_sca eq_refl.
  suff->: (fs_ca p : hrel E E) ≡ (fs_ica p : hrel E E)^*.
  - by symmetry; apply/str_itr_sub_one. 
  rewrite -clos_rt_str.
  move=> ?? /=; symmetry; apply: rwP; exact/fs_caP.
Qed.

Lemma supp_closed_sca p e1 e2 : supp_closed p -> acyclic (fin_ica p) -> 
  fs_sca p e1 e2 -> (e1 \in finsupp p) * (e2 \in finsupp p).
Proof. 
  move=> supcl acyc /(fs_scaP _ _ supcl acyc) /clos_t_itr.
  suff: (fs_ica p : hrel E E)^+ ≦ mem (finsupp p) × mem (finsupp p).   
  - by move=> /[apply] /= /andP[].
  etransitivity.
  - apply kleene.itr_leq=> ??.  
    by apply/supp_closedP.
  move=> ?? /clos_t_itr; elim=> //=.
  - move=> ?? [??]; exact/andP.
  by move=> ??? H1 /andP[??] H2 /andP[??]; apply/andP.
Qed.

Lemma supp_closed_ca p e1 e2 : supp_closed p -> acyclic (fin_ica p) -> 
  fs_ca p e1 e2 -> (e1 == e2) || (e1 \in finsupp p) && (e2 \in finsupp p).
Proof. 
  move=> supcl acyc. 
  rewrite fs_ca_scaE=> /orP[/eqP->|].
   - by rewrite eq_refl.
  move=> /(supp_closed_sca supcl acyc) [??].
  by apply/orP; right; apply/andP.  
Qed.

Lemma operationalP p : 
  supp_closed p -> acyclic (fin_ica p) -> 
  reflect 
    (subrel (fs_ca p) (<=^i%O))
    (operational p).
Proof.
  move=> sp ac; apply: (iffP forallP).
  - move=> /[swap] ? /[swap] ? /[swap] /[dup] ? /(supp_closed_ca sp ac).
    case/orP=> [/eqP->//|/andP[] in1 in2 /(_ [` in1]) /forallP/(_ [` in2])].
    move/implyP; exact.
  by move=> o [>]; apply/forallP=> -[>]; apply/implyP=> /o.
Qed.


Lemma fs_ica_irrefl p : supp_closed p -> irreflexive (fin_ica p) -> 
  irreflexive (fs_ica p).
Proof. 
  move=> supcl irr. 
  rewrite /fin_ica /fs_ica /sub_rel_down => e /=.
  case: (e \in finsupp p)/idP.
  - by move=> eIn; move: (irr (Sub e eIn))=> /=. 
  by move=> /negP nsupp; rewrite /fs_rcov fsfun_dflt //. 
Qed.

Lemma fs_ca_antisym p : supp_closed p -> acyclic (fin_ica p) -> 
  antisymmetric (fs_ca p).
Proof. 
  move=> supcl acyc e1 e2.
  rewrite /fs_ca /sub_rel_lift /= /dhrel_one.
  move=> /andP[] /orP[/eqP|] //.
  move=> /[swap] /orP[/eqP|] //.
  case: insubP=> // e2' in2 <-.
  case: insubP=> // e1' in1 <-.
  move=> ??; suff->: e1' = e2'=> //.
  move: (acyc_antisym acyc)=> anti.
  by apply/anti/andP.
Qed.

Lemma lfsp_dw_clos_subs p es : 
  {subset (lfsp_dw_clos p es) <= finsupp p}.
Proof. by move=> e; rewrite mem_filter=> /andP[]. Qed.

Lemma lfsp_dw_closP p es e : 
  supp_closed p -> acyclic (fin_ica p) -> es `<=` (finsupp p) ->
    reflect (exists2 e', fs_ca p e e' & e' \in es) (e \in lfsp_dw_clos p es).
Proof. 
  move=> supcl acyc /fsubsetP subs.
  rewrite mem_filter.
  apply/(equivP idP); split.
  - move=> /andP[] /existsP[e'] eCa eIn.
    exists (val e')=> //; exact/(valP e').
  move=> [e'] eCa e'In; apply/andP; split.
  - by apply/existsP; exists (Sub e' e'In).
  move: eCa; rewrite fs_ca_scaE=> /orP[/eqP->|].
  - exact/subs.
  (* TODO: looks like it can be proven with weaker assumptions *)
  by move=> /(supp_closed_sca supcl acyc) ->.
Qed.

Lemma fs_ca_ident_le p :
  supp_closed p -> acyclic (fin_ica p) -> operational p ->
  subrel (fs_ca p) <=^i%O.
Proof. move=>?? /operationalP; exact. Qed.

Lemma fin_lab_mono p : 
  {mono val : e / fin_lab p e >-> fs_lab p e}.
Proof. done. Qed.

Lemma fin_ica_mono p : 
  {mono val : x y / fin_ica p x y >-> fs_ica p x y}.
Proof. done. Qed.

Lemma fin_ca_mono p : 
  {mono val : x y / fin_ca p x y >-> fs_ca p x y}.
Proof. 
  move=> e1 e2; rewrite /fs_ca /= /dhrel_one.
  rewrite /sub_rel_lift /=.
  case: insubP; last first.
  - by move: (valP e1)=> + /negP.
  case: insubP; last first.
  - by move: (valP e2)=> + /negP.
  move=> e1' in1 /val_inj <- e2' in2 /val_inj <-.
  apply/orb_idl.
  move=> /eqP /val_inj ->.
  exact/connect0.
Qed.

End Theory.
End Theory.

Section Build.
Context (E : identType) (L : eqType) (bot : L). 
Context (fE : {fset E}).
Implicit Types (p : lfspreposet E L bot).
Implicit Types (lab : fE -> L) (ica : rel fE) (ca : rel E).

Definition build lab ica : lfspreposet E L bot := 
  let rcov e := [fsetval e' in rgraph [rel x y | ica y x] e] in
  [fsfun e => (lab e, rcov e)].

Definition build_cov lab ca : lfspreposet E L bot := 
  let sca : rel E := (fun x y => (y != x) && (ca x y)) in
  let ica : rel fE := cov (relpre val sca) in
  build lab ica.

Section Build.
Variables (lab : fE -> L) (ica : rel fE).
Hypothesis (labD : forall e, lab e != bot).

Lemma build_finsupp : 
  finsupp (build lab ica) = fE.
Proof.
  apply/fsetP=> ?.
  rewrite mem_finsupp fsfun_ffun.
  case: insubP=> [*|/negbTE-> /[! eqxx] //].
  by rewrite xpair_eqE (negbTE (labD _)).
Qed. 

Lemma build_lab : 
  fs_lab (build lab ica) =1 sub_lift (fun=> bot) lab.
Proof.
  rewrite /fs_lab /sub_lift=> ?.
  rewrite fsfun_ffun; by case: insubP.
Qed.

Lemma build_ica : 
  fs_ica (build lab ica) =2 sub_rel_lift ica.
Proof.
  rewrite /fs_ica /build /sub_rel_lift /fs_rcov.
  move=> x y /=; rewrite fsfun_ffun. 
  (do 2 case: insubP=> //=) => [u ?<- v*|+*].
  - rewrite ?inE; exact/rgraphK.
  by rewrite in_fsetval_seq; case: insubP=> // ? ->.
Qed.

Lemma lab_defined_build : 
  lab_defined (build lab ica).
Proof.
  apply/lab_definedP=>>.
  rewrite build_lab build_finsupp //.
  by move=> ? /[! @sub_liftT E].
Qed.

Lemma supp_closed_build : 
  supp_closed (build lab ica).
Proof.
  apply/supp_closedP=>>.
  rewrite build_ica build_finsupp //. 
  by move=> /sub_rel_liftP[[>[[>[? /= <- <-]]]]].
Qed.

Lemma acyclic_build :
  acyclic ica -> acyclic (fin_ica (build lab ica)).
Proof. 
  move=> acyc; rewrite acyclicE; apply/andP; split.
  - apply/irreflexiveP/irreflexive_mono; first exact/fin_ica_mono.
    move=> x /=; rewrite build_ica /= /sub_rel_lift /=.
    rewrite !insubT //= -?build_finsupp; first exact/(valP x).
    move=> x'; exact/acyc_irrefl.
  apply/antisymmetricP/antisymmetric_mono; first exact/fin_ca_mono. 
  move=> /= x y /andP[].
  pose supcl := supp_closed_build.
  move=> /(fs_caP _ _ supcl)/clos_rt_str + /(fs_caP _ _ supcl)/clos_rt_str.
  have eq_ica: (fs_ica (build lab ica) : hrel E E) ≡ sub_rel_lift ica.
  - by move=> ?? /=; rewrite build_ica.
  rewrite !(str_weq eq_ica) !sub_rel_lift_connect.
  have xIn: val x \in fE.
  - rewrite -build_finsupp; exact/(valP x).
  have yIn: val y \in fE.
  - rewrite -build_finsupp; exact/(valP y).
  move=> /= [/val_inj->|] // + [/val_inj->|] //.
  have->: val x = val (Sub (val x) xIn : fE) by done.
  have->: val y = val (Sub (val y) yIn : fE) by done.
  rewrite !sub_rel_lift_val=> ??.
  suff: (Sub (val x) xIn) = (Sub (val y) yIn : fE).
  - by move=> [] /val_inj.
  by apply/(acyc_antisym acyc)/andP.
Qed.  

End Build.

Section BuildCov.
Variables (lab : fE -> L) (ca : rel E).
Hypothesis (labD : forall e, lab e != bot).
Hypothesis (ca_refl  : reflexive ca).
Hypothesis (ca_anti  : antisymmetric ca).
Hypothesis (ca_trans : transitive ca).

Let sca : rel E  := (fun x y => (y != x) && (ca x y)).
Let ica : rel fE := cov (relpre val sca).

Lemma build_cov_fin_ica : 
  fin_ica (build_cov lab ca) =2 cov (relpre val sca).
Proof.
  case=> ? /[dup] + in1 [? /[dup] + in2]. 
  rewrite {1 2}build_finsupp => * //.
  rewrite /fin_ica /sub_rel_down /=.
  rewrite build_ica /sub_rel_lift /=.
  do ? case: insubP=> [??? |/negP//].
  move: in1 in2; case: _ / (esym (@build_finsupp lab ica labD))=> *.
  apply/congr2/val_inj=> //; exact/val_inj.
Qed.

(* TODO: generalize! *)
Lemma build_cov_connect_ca : 
  let D := finsupp (build_cov lab ca) in
  (connect (relpre val ca) : rel D) =2 relpre val ca.
Proof. 
  move=>>; apply/connect_eqP/rtclosedP. 
  split; move=>> /=; [exact/ca_refl | exact/ca_trans].
Qed.

(* TODO: generalize! *)
Lemma build_cov_connect_sca : 
  let D := finsupp (build_cov lab ca) in
  (connect (relpre val sca) : rel D) =2 connect (relpre val ca).
Proof. 
  move=>>; rewrite ?(connect_sub_one (relpre val ca)).
  apply eq_connect=> ?? /=.
  by rewrite /sca -(inj_eq val_inj) /= eq_sym.
Qed.

(* TODO: generalize! *)
Lemma build_cov_acyclic_sca : 
  let D := finsupp (build_cov lab ca) in
  acyclic (relpre val sca : rel D).
Proof. 
  apply/acyclicP; split=> [[/= ??]|]; first by rewrite /sca eq_refl.
  apply/preacyclicP=> ?? /andP[].
  rewrite !build_cov_connect_sca !build_cov_connect_ca /= => ??. 
  by apply/val_inj/ca_anti/andP.
Qed.

Lemma build_cov_acyclic : 
  acyclic (fin_ica (build_cov lab ca)).
Proof. 
  under eq_acyclic do rewrite build_cov_fin_ica. 
  apply/sub_acyclic; first exact/cov_subrel.
  exact/build_cov_acyclic_sca.
Qed.

Lemma build_cov_fin_ca : 
  fin_ca (build_cov lab ca) =2 (relpre val ca).
Proof.
  move=> x y; rewrite /fin_ca. 
  under eq_connect do rewrite build_cov_fin_ica. 
  rewrite -build_cov_connect_ca. 
  rewrite connect_covE ?build_cov_connect_sca //.
  exact/build_cov_acyclic_sca.
Qed.

(* TODO: reformulate in terms of relation-algebra? *)
Lemma build_cov_ca e1 e2 : 
  fs_ca (build_cov lab ca) e1 e2 = 
    (e1 == e2) || [&& ca e1 e2, e1 \in fE & e2 \in fE].
Proof. 
  move: e1 e2; rewrite /fs_ca.
  apply: qmk_weq_rel=> /= e1 e2.
  (* TODO: make a lemma? *)
  rewrite /sub_rel_lift /=.  
  case: insubP=> [e1'|]; rewrite {1}build_finsupp //; last first.
  - by move=> /negPf->; rewrite !andbF.
  move=> -> val1.
  case: insubP=> [e2'|]; rewrite {1}build_finsupp //; last first.
  - by move=> /negPf->; rewrite !andbF.
  move=> -> val2. 
  by rewrite build_cov_fin_ca /= val1 val2 andbT. 
Qed.

End BuildCov.

End Build.

Section Empty.
Context (E : identType) (L : eqType) (bot : L). 
Implicit Types (p : lfspreposet E L bot).

Definition empty : lfspreposet E L bot := [fsfun].

Lemma fs_lab_empty : 
  fs_lab empty =1 (fun=> bot).
Proof. by move=> ?; rewrite /fs_lab fsfun_dflt ?inE. Qed.

Lemma fs_ica_empty : 
  fs_ica empty =2 (fun x y => false).
Proof. by move=> ??; rewrite /fs_ica /= /fs_rcov !fsfun_dflt ?inE. Qed.

(* TODO: /start/ the following proofs should be simpler :( *)

Lemma fin_ica_empty : 
  fin_ica empty =2 (fun x y => false). 
Proof. 
  rewrite /fin_ica /sub_rel_down /= => ?? /=. 
  by rewrite fs_ica_empty.
Qed.

Lemma fin_ca_empty : 
  fin_ca empty =2 (fun x y => x == y). 
Proof. 
  move=> e1 e2; rewrite /fin_ca.
  apply/idP/idP; last first.
  - move=> /eqP ->; exact/connect_refl.
  move=> /connect_strP/clos_rt_str; elim=> //.
  - by move=> ??; rewrite fin_ica_empty. 
  by move=> ???? /eqP-> ? /eqP->.
Qed.
  
Lemma fs_ca_empty : 
  fs_ca empty =2 (fun x y => x == y).
Proof. 
  move=> e1 e2; rewrite /fs_ca /= /dhrel_one.
  apply/orb_idr; rewrite /sub_rel_lift /=.
  case: insubP=> // e1' in1 <-.
  case: insubP=> // e2' in2 <-.
  by rewrite fin_ca_empty=> /eqP ->.
Qed.

(* TODO: /end/ the following proofs should be simpler :( *)

Lemma empty_lab_defined : 
  lab_defined empty.
Proof. by apply/lab_definedP=> ?; rewrite fs_lab_empty inE. Qed.

Lemma empty_supp_closed : 
  supp_closed empty.
Proof. by apply/supp_closedP=> ??; rewrite fs_ica_empty. Qed.

Lemma empty_acyclic : 
  acyclic (fin_ica empty).
Proof. 
  apply/acyclicP; split.
  - by move=> ?; rewrite /fin_ica /sub_rel_down /= fs_ica_empty.
  apply/forall2P=> e1 e2. 
  apply/implyP=> /andP[].
  have->: connect (fin_ica empty) e1 e2 = fin_ca empty e1 e2 by done.
  by rewrite fin_ca_empty=> /eqP->. 
Qed.

End Empty.

Arguments empty E L bot : clear implicits.

Section OfSeq.
Context (E : identType) (L : eqType) (bot : L). 
Implicit Types (p : lfspreposet E L bot).
Implicit Types (ls : seq L).

Definition of_seq ls := 
  let fE  := [fset e | e in nfresh \i1 (size ls)] in 
  let lab := fun e : fE => (nth bot (bot :: ls) (encode (val e))) in
  let ca  := fun e1 e2 : E => e1 <=^i e2 in
  @build_cov E L bot fE lab ca.

Variable (ls : seq L).
Hypothesis (lsD : bot \notin ls).

Lemma of_seq_nth_defined : 
  forall (e : [fset e | e in nfresh \i1 (size ls)]),
    nth bot (bot :: ls) (@encode E (val e)) != bot.
Proof.
  move: lsD=> /negP nbl [/= ?].
  rewrite ?inE /= in_nfresh encode1; case: (encode _)=> //> ?.
  apply/negP; move: nbl=> /[swap]/eqP<-.
  apply; apply/mem_nth; lia.
Qed.

Lemma of_seq_finsupp : 
  finsupp (of_seq ls) = [fset e | e in nfresh \i1 (size ls)].
Proof. rewrite build_finsupp //; exact/of_seq_nth_defined. Qed.

Lemma of_seq_labE e : 
  fs_lab (of_seq ls) e = nth bot (bot :: ls) (encode e).
Proof.
  rewrite /of_seq build_lab /= /sub_lift.
  case: insubP=> /= [?? ->|] //.
  rewrite !in_fset /mem_fin /=.
  rewrite in_nfresh encode1.
  rewrite negb_and ltnNge negbK addn1 -ltnNge leqn0 ltnS.
  case/orP=>[/eqP-> //|].
  by move=> ?; rewrite nth_default.
Qed.

Lemma of_seq_fs_caE e1 e2 : 
  fs_ca (of_seq ls) e1 e2 = 
    (e1 == e2) ||
    [&& e1 <=^i e2
      , e1 \in finsupp (of_seq ls)
      & e2 \in finsupp (of_seq ls)
    ].
Proof. 
  rewrite of_seq_finsupp /of_seq. 
  rewrite build_cov_ca // => [? ||]; last first.
  - exact/le_trans.
  - exact/le_anti.
  by rewrite of_seq_nth_defined.
Qed.

Lemma of_seq_lab_defined : 
  lab_defined (of_seq ls).
Proof. exact/lab_defined_build/of_seq_nth_defined. Qed.

Lemma of_seq_supp_closed : 
  supp_closed (of_seq ls).
Proof.
  apply/supp_closedP=>>.
  rewrite build_ica build_finsupp //; last first. 
  - exact/of_seq_nth_defined.
  by move=> /sub_rel_liftP[[>[[>[? /= <- <-]]]]].
Qed.

Lemma of_seq_fin_ica_acyclic : 
  acyclic (fin_ica (of_seq ls)).
Proof.
  apply/build_cov_acyclic=> [? |||]; last first.
  - exact/le_trans.
  - exact/le_anti.
  - exact/le_refl.
  by rewrite of_seq_nth_defined.
Qed.

End OfSeq.

Arguments of_seq E L bot : clear implicits.

Section Intersection.
Context (E : identType) (L : eqType) (bot : L). 
Implicit Types (p : lfspreposet E L bot).
Implicit Types (r : rel E).

Definition inter p r := 
  @build_cov E L bot _ (fin_lab p) (r ⊓ (fs_ca p)).

Lemma inter_finsupp p r : 
  lab_defined p -> finsupp (inter p r) = finsupp p.
Proof. by move=> ?; rewrite build_finsupp //; apply/forallP. Qed.

Lemma inter_labE p r : 
  fs_lab (inter p r) =1 fs_lab p.
Proof.
  move=> e; rewrite /inter build_lab. 
  case: (e \in finsupp p)/idP=> [eIn | enIn].
  - by rewrite sub_liftT. 
  rewrite sub_liftF // /fs_lab fsfun_dflt //. 
  exact/negP.    
Qed.

Lemma inter_lab_defined p r : 
  lab_defined p -> lab_defined (inter p r).
Proof. move=> labD; apply/lab_defined_build; exact/forallP. Qed.

Lemma inter_supp_closed p r : 
  lab_defined p -> supp_closed p -> supp_closed (inter p r).
Proof.
  move=> labD supcl; apply/supp_closedP=>>.
  rewrite build_ica build_finsupp //; last first. 
  - move=> ?; rewrite /fin_lab; apply/lab_definedP=> //; exact/valP. 
  by move=> /sub_rel_liftP[[>[[>[? /= <- <-]]]]].
Qed.

Lemma inter_acyclic p r : 
  lab_defined p -> acyclic (fin_ica p) -> acyclic (fin_ica (inter p r)).
Proof. 
  move=> labD acyc; apply/build_cov_acyclic.
  - move=> e; apply/lab_definedP=> //; exact/valP.
  - 

End Intersection.

End lFsPrePoset.

Export lFsPrePoset.Def.
Export lFsPrePoset.Theory.


Module lFsPoset.

Module Export Def.
Section Def. 
Context (E : identType) (L : eqType).
Variable (bot : L).

Structure lfsposet : Type := lFsPoset {
  lfsposet_val :> lfspreposet E L bot ; 
  _ : let p := lfsposet_val in 
      [&& lab_defined p, supp_closed p & acyclic (fin_ica p)]
}.

Canonical lfsposet_subType := Eval hnf in [subType for lfsposet_val].

Implicit Types (p : lfsposet).

Lemma lfsp_lab_defined p : lab_defined p.
Proof. by move: (valP p)=> /and3P[]. Qed.

Lemma lfsp_supp_closed p : supp_closed p.
Proof. by move: (valP p)=> /and3P[]. Qed.

Lemma lfsp_acyclic p : acyclic (fin_ica p).
Proof. by move: (valP p)=> /and3P[]. Qed.

End Def.
End Def.

Arguments lfsposet E L bot : clear implicits.

Module Export Instances.
Section Instances. 

Definition lfsposet_eqMixin E L bot := 
  Eval hnf in [eqMixin of (lfsposet E L bot) by <:].
Canonical lfinposet_eqType E L bot := 
  Eval hnf in EqType (lfsposet E L bot) (@lfsposet_eqMixin E L bot).

Definition lfsposet_choiceMixin E (L : choiceType) bot :=
  Eval hnf in [choiceMixin of (lfsposet E L bot) by <:].
Canonical lfsposet_choiceType E (L : choiceType) bot :=
  Eval hnf in ChoiceType (lfsposet E L bot) (@lfsposet_choiceMixin E L bot).

Definition lfsposet_countMixin E (L : countType) bot :=
  Eval hnf in [countMixin of (@lfsposet E L bot) by <:].
Canonical lfsposet_countType E (L : countType) bot :=
  Eval hnf in CountType (lfsposet E L bot) (@lfsposet_countMixin E L bot).

Canonical subFinfun_subCountType E (L : countType) bot :=
  Eval hnf in [subCountType of (lfsposet E L bot)].

End Instances.
End Instances.

Section Empty.
Context (E : identType) (L : eqType) (bot : L). 
Implicit Types (p : lfspreposet E L bot).

(* TODO: rename? *)
Lemma emptyP : 
  let p := @lFsPrePoset.empty E L bot in
  [&& lab_defined p,
      supp_closed p &
      acyclic (fin_ica p)].
Proof.
  apply/and3P; split.
  - exact/lFsPrePoset.empty_lab_defined.
  - exact/lFsPrePoset.empty_supp_closed.
  exact/lFsPrePoset.empty_acyclic.
Qed.

Definition empty : lfsposet E L bot := 
  lFsPoset emptyP.

End Empty.

Arguments empty E L bot : clear implicits.

Section OfSeq.
Context (E : identType) (L : eqType) (bot : L). 
Implicit Types (p : lfspreposet E L bot).
Implicit Types (ls : seq L).

Lemma of_seqP ls : bot \notin ls -> 
  let p := lFsPrePoset.of_seq E L bot ls in
  [&& lab_defined p,
      supp_closed p &
      acyclic (fin_ica p)].
Proof.
  move=> labD; apply/and3P; split.
  - exact/lFsPrePoset.of_seq_lab_defined.
  - exact/lFsPrePoset.of_seq_supp_closed.
  exact/lFsPrePoset.of_seq_fin_ica_acyclic.
Qed.

Definition of_seq ls : lfsposet E L bot := 
  if bot \notin ls =P true is ReflectT nbl then
    lFsPoset (of_seqP nbl)
  else empty E L bot.

Variable (ls : seq L).
Hypothesis (lsD : bot \notin ls).

Lemma of_seq_valE : 
  val (of_seq ls) = lFsPrePoset.of_seq E L bot ls.
Proof. rewrite /of_seq; case: eqP=> //. Qed.

(* Lemma of_seq_labE e :  *)
(*   fs_lab (of_seq ls) e = nth bot ls (encode e). *)
(* Proof. rewrite /of_seq; case: eqP=> //. Qed. *)

End OfSeq.

Arguments of_seq E L bot : clear implicits.

Module Export POrder.
Section POrder.
Context {E : identType} {L : eqType}.
Variable (bot : L) (p : lfsposet E L bot).

Lemma fs_sca_def e1 e2 : 
  fs_sca p e1 e2 = (e2 != e1) && (fs_ca p e1 e2).
Proof. done. Qed.
 
Lemma fs_ca_refl : 
  reflexive (fs_ca p). 
Proof. move=> ?; apply/(fs_caP _ _ (lfsp_supp_closed p))/rt_refl. Qed.

Lemma fs_ca_trans : 
  transitive (fs_ca p). 
Proof. 
  move=> y x z.
  move=> /(fs_caP _ _ (lfsp_supp_closed p)) ca_xy.
  move=> /(fs_caP _ _ (lfsp_supp_closed p)) ca_yz.
  apply/(fs_caP _ _ (lfsp_supp_closed p)). 
  apply/rt_trans; [exact/ca_xy | exact/ca_yz].
Qed. 

Lemma fs_ca_antisym : 
  antisymmetric (fs_ca p). 
Proof. 
  move=> e1 e2 /andP[]; rewrite /fs_ca /=.
  rewrite /dhrel_one=> /orP[/eqP->|+ /orP[/eqP<-|]] //. 
  move=> /sub_rel_liftP + /sub_rel_liftP.
  move=> [e1' [] e2' [+++]] [e3' [] e4' [+++]].
  move=> /[swap] <- /[swap] <-.
  move=> ++ /val_inj H1 /val_inj H2.
  rewrite H2 H1=> con_e12 con_e21.
  suff: e1' = e2'=> [->|] //.
  by apply/(acyc_antisym (lfsp_acyclic p))/andP.
Qed.  

Definition lfsposet_porderMixin := 
  @LePOrderMixin E (fs_ca p) (fs_sca p) 
    fs_sca_def fs_ca_refl fs_ca_antisym fs_ca_trans. 

Definition lfsposet_porderType := 
  POrderType tt E lfsposet_porderMixin.

Definition lfsposet_lposetMixin := 
  @lPoset.lPoset.Mixin E L (Order.POrder.class lfsposet_porderType) (fs_lab p).

Definition lfsposet_lposetType := 
  @lPoset.lPoset.Pack L E (lPoset.lPoset.Class lfsposet_lposetMixin).

End POrder.
End POrder.

Module Export FinPOrder.
Section FinPOrder.
Context (E : identType) (L : eqType) (bot : L).
Variable (p : lfsposet E L bot).

Lemma fin_sca_def e1 e2 : 
  fin_sca p e1 e2 = (e2 != e1) && (fin_ca p e1 e2).
Proof. done. Qed.

Lemma fin_ca_refl : 
  reflexive (fin_ca p).
Proof. exact/connect_refl. Qed.

Lemma fin_ca_antisym : 
  antisymmetric (fin_ca p).
Proof. exact/acyc_antisym/(lfsp_acyclic p). Qed.

Lemma fin_ca_trans : 
  transitive (fin_ca p).
Proof. exact/connect_trans. Qed.

Lemma fin_disp : unit. 
Proof. exact: tt. Qed.

Definition lfsposet_fin_porderMixin := 
  @LePOrderMixin _ (fin_ca p) (fin_sca p) 
    fin_sca_def fin_ca_refl fin_ca_antisym fin_ca_trans. 

Definition lfsposet_fin_porderType := 
  POrderType fin_disp _ lfsposet_fin_porderMixin.

Definition lfsposet_FinPOrderType :=
  [finPOrderType of lfsposet_fin_porderType].

Definition lfsposet_fin_lposetMixin := 
  @lPoset.lPoset.Mixin _ L (Order.POrder.class lfsposet_fin_porderType) (fin_lab p).

Definition lfsposet_fin_lposetType := 
  @lPoset.lPoset.Pack L (lfsposet_FinPOrderType) (lPoset.lPoset.Class lfsposet_fin_lposetMixin).

Definition lfsposet_lfinposetType :=
  let finCls := Order.FinPOrder.class lfsposet_FinPOrderType in
  let cls := @lFinPoset.lFinPoset.Class _ L finCls lfsposet_fin_lposetMixin in
  @lFinPoset.lFinPoset.Pack L _ cls.

End FinPOrder.
End FinPOrder.

Module Export bHom.
Section bHom.
Implicit Types (E : identType) (L : eqType).

Import lPoset.Syntax.

(* TODO: rename bhom_preord? *)
Definition bhom_le E1 E2 L bot : lfsposet E1 L bot -> lfsposet E2 L bot -> bool 
  := fun p q => 
       let EP := [FinEvent of p] in
       let EQ := [FinEvent of q] in
       ??|{ffun EQ -> EP | lFinPoset.bhom_pred}|.

(* TODO: this relation should also be heterogeneous? *)
Definition bhom_lt E L bot : rel (lfsposet E L bot) := 
  fun p q => (q != p) && (bhom_le p q).

Definition lin E L bot (p : lfsposet E L bot) : pred (seq L) :=
  [pred ls | bhom_le (lFsPoset.of_seq E L bot ls) p].


(* TODO: `f` can be declared {hom [Event of q] -> [Event of p]} ? *)
Lemma bhom_leP E1 E2 L bot (p : lfsposet E1 L bot) (q : lfsposet E2 L bot) :
  reflect 
    (exists f : [Event of q] -> [Event of p], 
      [/\                    { mono f : e / lab e }
        , {in (finsupp q) &, { homo f : e1 e2 / e1 <= e2 }}
        & {on (finsupp p)  , bijective f} 
      ])
    (bhom_le p q).
Proof. 
  rewrite /bhom_le; apply/(equivP idP); split; last first.
  - move=> [f] [] flab fca fbij.
    apply/lFinPoset.fbhomP. 
    move: fbij=> [g] K K'.  
    have map_suppf : forall e, e \in finsupp q -> (f e) \in finsupp p.
    + move=> e /[dup] eIn; rewrite -fs_labNbot -fs_labNbot -fs_labE -fs_labE.
      by move=> /eqP labD; apply/eqP; rewrite flab.  
    have map_suppf' : forall e, (f e) \in finsupp p -> e \in finsupp q.
    + by move=> e /[dup] eIn; rewrite -fs_labNbot -fs_labNbot -fs_labE -fs_labE flab.
    have map_suppg : forall e, e \in finsupp p -> (g e) \in finsupp q.
    + move=> e /[dup] eIn; rewrite -fs_labNbot -fs_labNbot -fs_labE -fs_labE.
      by rewrite -flab; apply/contra; rewrite K'.
    pose f' : [FinEvent of q] -> [FinEvent of p] := 
      fun e => Sub (f (val e)) (map_suppf (val e) (valP e)). 
    pose g' : [FinEvent of p] -> [FinEvent of q] := 
      fun e => Sub (g (val e)) (map_suppg (val e) (valP e)). 
    eexists=> /=; exists f'; repeat constructor=> /=.
    + move=> e; rewrite !fin_labE /f' /fin_lab /= -fs_labE -fs_labE flab //. 
    + move=> e1 e2; rewrite !fin_caE /f'. 
      rewrite -fin_ca_mono -fin_ca_mono /=. 
      by rewrite -fs_caE -fs_caE; apply/fca.
    exists g'=> e; rewrite /f' /g' /=; apply/val_inj=> /=; rewrite ?K ?K'=> //. 
    exact/map_suppf.
  move=> /lFinPoset.fbhomP [f].
  pose g := lPoset.bHom.invF f.
  pose f' : [Event of q] -> [Event of p] := 
    sub_lift (fun e => fresh_seq (finsupp p)) 
             (fun e => val (f e)).
  pose g' : [Event of p] -> [Event of q] := 
    sub_lift (fun e => fresh_seq (finsupp q)) 
             (fun e => val (g e)).
  exists f'; split.
  - move=> e.
    case: (e \in finsupp q)/idP=> [eIn|/negP eNIn]; last first.
    + rewrite /f' sub_liftF // ?fs_labE ?fs_lab_bot //; last exact/negP.
      exact/fresh_seq_nmem.               
    rewrite /f' sub_liftT // !fs_labE.
    have {2}->: e = val (Sub e eIn : [FinEvent of q]) by done.
    rewrite !fin_lab_mono -fin_labE -fin_labE.
    exact/(lab_preserving f).
  - move=> e1 e2 in1 in2; rewrite /f' !sub_liftT !fs_caE.
    have {1}->: e1 = val (Sub e1 in1 : [FinEvent of q]) by done.  
    have {1}->: e2 = val (Sub e2 in2 : [FinEvent of q]) by done.  
    rewrite !fin_ca_mono -fin_caE -fin_caE.
    exact/(ca_monotone f).
  exists g'=> /= e /=; last first. 
  - move=> eIn; rewrite /f' /g' !sub_liftT //= => gIn.
    suff->: (f.[gIn] = f (g.[eIn]))%fmap by rewrite can_inv.
    by f_equal; apply/val_inj=> /=.
  case: (e \in finsupp q)/idP; last first.
  - move=> nIn; rewrite /f' sub_liftF=> //.
    by move: (fresh_seq_nmem (finsupp p))=> /negP.
  move=> eIn; rewrite /g' /f' !sub_liftT => //= fIn _.
  suff->: (g.[fIn] = g (f.[eIn]))%fmap by rewrite /g inv_can.
  by f_equal; apply/val_inj=> /=.
Qed.

Context (E : identType) (L : eqType) (bot : L).
Implicit Types (p q : lfsposet E L bot).

Lemma bhom_lt_def p q : bhom_lt p q = (q != p) && (bhom_le p q).
Proof. done. Qed.

Lemma bhom_le_refl : reflexive (@bhom_le E E L bot). 
Proof. move=> ?; exact/lFinPoset.bhom_refl. Qed.

Lemma bhom_le_trans : transitive (@bhom_le E E L bot). 
Proof. move=> ??? /[swap]; exact/lFinPoset.bhom_trans. Qed.

End bHom.
End bHom.

End lFsPoset.

Export lFsPoset.Def.
Export lFsPoset.Instances.
Export lFsPoset.Syntax.
Export lFsPoset.Theory.
Export lFsPoset.bHom.


Module Pomset.

Import lPoset.Syntax.
Import lFsPoset.Syntax.

Module Export Def.
Section Def.  
Context {E : identType} {L : choiceType} {bot : L}.

(* TODO: rename iso_equiv? *)
Definition is_iso : rel (@lfsposet E L bot) := 
  fun p q => 
    ??|{ffun [FinEvent of p] -> [FinEvent of q] | lFinPoset.iso_pred}|.

(* TODO: generalize the proofs to arbitary `T -> T -> Type`? *)
Lemma is_iso_refl : reflexive is_iso.
Proof. 
  rewrite /is_iso=> p.
  apply/lFinPoset.fisoP; 
  exists; exact/[iso of idfun]. 
Qed.

Lemma is_iso_sym : symmetric is_iso.
Proof. 
  rewrite /is_iso=> p q.
  apply/idP/idP=> /lFinPoset.fisoP [f]; 
    apply/lFinPoset.fisoP; 
    (* TODO: [iso of ...] notation for inverse *)
    exists; exact/(lPoset.Iso.Build.inv f).
Qed.

Lemma is_iso_trans : transitive is_iso.
Proof. 
  rewrite /is_iso=> p q r.
  move=> /lFinPoset.fisoP [f] /lFinPoset.fisoP [g]. 
  apply/lFinPoset.fisoP. 
  exists; exact/[iso of g \o f].
Qed.

Canonical is_iso_eqv := EquivRel is_iso is_iso_refl is_iso_sym is_iso_trans.

Definition pomset := {eq_quot is_iso}.

Canonical pomset_quotType := [quotType of pomset].
Canonical pomset_eqType := [eqType of pomset].
Canonical pomset_choiceType := [choiceType of pomset].
Canonical pomset_eqQuotType := [eqQuotType is_iso of pomset].

Definition pom : lfsposet E L bot -> pomset := \pi.

Implicit Types (p : pomset).

Coercion lfsposet_of p : lfsposet E L bot := repr p.

End Def.
End Def.

Arguments pomset E L bot : clear implicits.

Module Export Hom.
Module Export POrder.
Section POrder.
Implicit Types (E : identType) (L : choiceType).

Import lPoset.Syntax.
Import lFsPoset.Syntax.

Lemma pi_bhom_le E1 E2 L bot (p : lfsposet E1 L bot) (q : lfsposet E2 L bot) :
  bhom_le (repr (pom p)) (repr (pom q)) = bhom_le p q.
Proof.
  rewrite /bhom_le. 
  case: piP piP=> q' /eqmodP/lFinPoset.fisoP[f] [p' /eqmodP/lFinPoset.fisoP[g]].
  apply/lFinPoset.fbhomP/lFinPoset.fbhomP=> [][h]; exists.
  - exact/[bhom of lPoset.Iso.Build.inv g \o h \o f].
  exact/[bhom of g \o h \o lPoset.Iso.Build.inv f].
Qed.

Context {E : identType} {L : choiceType} {bot : L}.
Implicit Types (p q : pomset E L bot). 

Lemma pi_bhom_mono :
  {mono \pi_(pomset E L bot) : p q / bhom_le p q >-> bhom_le (repr p) (repr q)}.
Proof. exact/pi_bhom_le. Qed.

Canonical bhom_le_quote_mono2 := PiMono2 pi_bhom_mono.

(* TODO: use bhom_le_refl *)
Lemma pom_bhom_le_refl : 
  reflexive (@bhom_le E E L bot : rel (pomset E L bot)). 
Proof. move=> ?; exact/lFinPoset.bhom_refl. Qed.

(* TODO: use bhom_le_trans *)
Lemma pom_bhom_le_trans : 
  transitive (@bhom_le E E L bot : rel (pomset E L bot)). 
Proof. move=> ??? /[swap]; exact/lFinPoset.bhom_trans. Qed.

(* TODO: move part of the proof to lposet.v (or lFsPoset) ? *)
Lemma pom_bhom_le_antisym : 
  antisymmetric (@bhom_le E E L bot : rel (pomset E L bot)). 
Proof.
  move=> p q; rewrite -[p]reprK -[q]reprK !piE.
  case/andP=> /lFinPoset.fbhomP[f] /lFinPoset.fbhomP[g].
  apply/eqmodP/lFinPoset.fisoP; exists; exact/(lFinPoset.of_ihoms g f).
Qed.

Lemma disp : unit. 
Proof. exact: tt. Qed.

Definition pomset_bhomPOrderMixin := 
  @LePOrderMixin _ 
    (@bhom_le E E L bot : rel (pomset E L bot)) 
    (fun p q => (q != p) && (bhom_le p q))
    (fun p q => erefl) pom_bhom_le_refl pom_bhom_le_antisym pom_bhom_le_trans. 

Canonical pomset_bhomPOrderType := 
  POrderType disp (pomset E L bot) pomset_bhomPOrderMixin.

(* TODO: rename pom_bhom_leE? *)
Lemma bhom_leE p q : p <= q = bhom_le p q.
Proof. done. Qed.

End POrder.
End POrder.
End Hom.

Module Export Theory.
Section Theory.
Context {E : identType} {L : choiceType} (bot : L).
Implicit Types (p q : pomset E L bot).

Lemma bhom_lin p q :
  p <= q -> {subset (lin p) <= (lin q)}.
Proof.
  move=> pLq ?; rewrite /lin ?/(_ \in _) /=.
  by move=> //= /bhom_le_trans /(_ pLq).
Qed.

End Theory.
End Theory.

End Pomset.

Export Pomset.Def.
Export Pomset.Hom.POrder.
Export Pomset.Theory.

(* Context (E : identType) (L : choiceType) (bot : L). *)
(* Variables (p q : pomset E L bot). *)
(* Variables (e1 e2 : E). *)
(* Check (e1 <= e2 :> [Event of p]). *)
(* Check (e1 <= e2 :> [Event of q]). *)
(* Check (p <= q). *)

Module Tomset.

Import lPoset.Syntax.
Import lFsPoset.Syntax.

Module Export Def.
Section Def.  
Context (E : identType) (L : choiceType).
Variable (bot : L).

Structure tomset : Type := mkTomset {
  tomset_val :> pomset E L bot;
  _ : totalb (fin_ca tomset_val); 
}.

Canonical tomset_subType := Eval hnf in [subType for tomset_val].

Implicit Types (t : tomset) (ls : seq L).

Lemma tomset_total t : 
  total (<=%O : rel [FinEvent of t]).
Proof. by move: (valP t)=> /totalP. Qed.

Lemma tomset_total_in t : 
  {in (finsupp t) &, total (<=%O : rel [Event of t])}.
Proof. 
  move=> x y xIn yIn.
  pose x' := (Sub x xIn) : [FinEvent of t].
  pose y' := (Sub y yIn) : [FinEvent of t].
  move: (tomset_total x' y'). 
  rewrite /x' /y'.
  by move=> /orP[|] /val_ca_mon /= ->. 
Qed.

End Def.
End Def.

Arguments tomset E L bot : clear implicits.

Module Export Theory.
Section Theory.
Context {E : identType} {L : choiceType}.
Variable (bot : L).
Implicit Types (t : tomset E L bot).

(* Lemma tomset_labelsK : 
  cancel (@lfsp_labels E L bot) (@lFsPrePoset.of_seq E L bot).
Proof. admit. Admitted. *)

End Theory.
End Theory.

End Tomset.


Export Tomset.Def.
Export Tomset.Theory.

Module Export AddEvent.

Module Export Def.
Section Def.  
Context (E : identType) (L : choiceType) (bot : L).
Implicit Types (l : L) (es : {fset E}).
Implicit Types (p : lfspreposet E L bot).

Definition lfspre_add_event l es p : lfspreposet E L bot := 
  let e := lfsp_fresh p in
  [fsfun p with e |-> (l, es)].

End Def.
End Def.

Module Export Theory.
Section Theory.  
Context (E : identType) (L : choiceType) (bot : L).
Variable (l : L) (es : {fset E}).
Variable (p : lfspreposet E L bot).

Hypothesis (lD : l != bot).
Hypothesis (esSub : es `<=` finsupp p).

Lemma add_event_finsuppE :
  finsupp (lfspre_add_event l es p) = (lfsp_fresh p) |` (finsupp p).
Proof. 
  rewrite finsupp_with xpair_eqE.
  case: ifP=> [/andP[/eqP]|] //.
  by move: lD=> /eqP.
Qed.

Lemma add_event_fs_labE e :
  fs_lab (lfspre_add_event l es p) e = 
    if e == lfsp_fresh p then l else fs_lab p e. 
Proof. by rewrite /fs_lab /lfspre_add_event fsfun_withE; case: ifP. Qed.

Lemma add_event_fs_rcovE e :
  fs_rcov (lfspre_add_event l es p) e = 
    if e == lfsp_fresh p then es else fs_rcov p e. 
Proof. by rewrite /fs_rcov /lfspre_add_event fsfun_withE; case: ifP. Qed.

Lemma add_event_fs_icaE e1 e2 :
  fs_ica (lfspre_add_event l es p) e1 e2 = 
    (e1 \in es) && (e2 == lfsp_fresh p) || (fs_ica p e1 e2).
Proof. 
  rewrite /fs_ica /= !add_event_fs_rcovE.
  case: ifP=> [/eqP->|]; last first.
  - by rewrite andbF.
  rewrite andbT /fs_rcov fsfun_dflt /= ?inE ?orbF //. 
  exact/fresh_seq_nmem.
Qed.

Lemma add_event_lab_defined :
  lab_defined p -> lab_defined (lfspre_add_event l es p).
Proof.  
  move=> labD; apply/lab_definedP. 
  rewrite add_event_finsuppE // => e.
  rewrite !inE add_event_fs_labE=> /orP[|].  
  - by move=> /eqP-> //; rewrite eq_refl.
  move=> eIn; case: ifP=> [|_]; last first.
  - exact/lab_definedP.
  move: eIn=> /[swap] /eqP-> eIn.
  exfalso; move: eIn=> /negP; apply.
  rewrite /lfsp_fresh. 
  exact/negP/fresh_seq_nmem.
Qed.

Lemma add_event_supp_closed :
  supp_closed p -> supp_closed (lfspre_add_event l es p).
Proof.  
  move=> supcl.
  apply/supp_closedP=> e1 e2.
  rewrite add_event_finsuppE //.
  rewrite add_event_fs_icaE !inE. 
  move=> /orP[/andP[]|].
  - move=> in1 /eqP ->. 
    rewrite eq_refl orTb; split=> //.
    apply/orP; right; exact/(fsubsetP esSub).
  move=> /supp_closedP H.
  by move: (H supcl)=> [-> ->]. 
Qed.

Lemma add_event_fs_caE e1 e2 : supp_closed p -> acyclic (fin_ica p) ->
  fs_ca (lfspre_add_event l es p) e1 e2 = 
    (e1 \in lfsp_dw_clos p es) && (e2 == lfsp_fresh p) || (fs_ca p e1 e2).
Proof. 
  (* TODO: yet another terrible proof due to poor 
   *   integration of mathcomp & relation-algebra 
   *)
  move=> supcl acyc.
  apply/eq_bool_iff; apply: iff_trans.
  - apply: iff_sym; apply: rwP. 
    by apply/fs_caP/add_event_supp_closed.
  rewrite clos_rt_str.
  rewrite str_weq; last first.
  - move=> /= e1' e2'; apply/eq_bool_iff.
    by rewrite add_event_fs_icaE.
  pose r : hrel E E := 
    (fun e1' e2' => (e1' \in es) && (e2' == lfsp_fresh p) || fs_ica p e1' e2').
  pose r1 : hrel E E := 
    (fun e1' e2' => (e1' \in es) && (e2' == lfsp_fresh p)).
  pose r2 : hrel E E := 
    (fun e1' e2' => fs_ica p e1' e2').
  rewrite -/r.
  have reqv : (r ≡ (r2 ⊔ r1)).
  - rewrite cupC /r /r1 /r2=> {}e1 {}e2 /=. 
    by split=> /orP. 
  rewrite (str_weq reqv) kleene.str_pls.
  have H: forall e1' e2', (r2^* ⋅ r1) e1' e2' <-> 
        (e1' \in lfsp_dw_clos p es) && (e2' == lfsp_fresh p).
  - move=> {}e1 {}e2; rewrite /r1 /r2; split.
    + move=> [e3] /clos_rt_str/(fs_caP _ _ supcl) + /andP[+] /eqP->.
      rewrite eq_refl andbT=> ??.
      by apply/lfsp_dw_closP=> //; exists e3.
    move=> /andP[] /(lfsp_dw_closP _ supcl acyc esSub) [e3] ++ /eqP->.    
    move=> ??; exists e3; rewrite ?eq_refl ?andbT //.
    by apply/clos_rt_str/(fs_caP _ _ supcl).
  suff->: (r2^* ⋅ (r1 ⋅ r2^*)^*) e1 e2 <-> ((r2^* ⋅ r1) ⊔ r2^*) e1 e2.
  - split=> [[|]|].
    + by move=> /H ->.
    + move=> ca12; apply/orP; right; apply/fs_caP=> //.
      by apply/clos_rt_str.
    move=> /orP[|].
    + by move=> /H ?; left.
    by move=> /(fs_caP _ _ supcl)/clos_rt_str ?; right.
  suff: r2^*⋅(r1⋅r2^*)^* ≡ r2^*⋅r1 + r2^*.
  - by move=> ->. 
  have->: r1 ⋅ r2^* ≡ r1.
  - rewrite str_unfold_l dotxpls dotA.
    have->: r1 ⋅ r2 ≡ 0%ra; last by kat.
    move=> {}e1 {}e2 /=; split=> //.
    rewrite /r1 /r2 /hrel_dot=> [[e3]].        
    move=> /andP[] ? /eqP->.
    rewrite /lfsp_fresh.
    move=> /(supp_closedP _ supcl)=> [[+ _]].
    by move: (fresh_seq_nmem (finsupp p))=> /negP.
  have->: r1^* ≡ 1 ⊔ r1.
  - rewrite str_unfold_l; apply/qmk_weq.
    rewrite str_unfold_l dotxpls dotA.
    have->: r1 ⋅ r1 ≡ 0%ra; last by kat.
    move=> {}e1 {}e2 /=; split=> //.
    rewrite /r1 /r2 /hrel_dot=> [[e3]].        
    move=> /andP[] ? /eqP-> /andP[+ _].
    move: esSub=> /fsubsetP /[apply].
    rewrite /lfsp_fresh.
    by move: (fresh_seq_nmem (finsupp p))=> /negP.
  ka.    
Qed.  

Lemma add_event_irrefl : supp_closed p -> 
  irreflexive (fin_ica p) -> irreflexive (fin_ica (lfspre_add_event l es p)).
Proof. 
  move=> supcl irr.  
  apply/irreflexive_mono.
  - exact/fin_ica_mono.
  move=> /=; case=> e /=. 
  rewrite add_event_finsuppE !add_event_fs_icaE /lfsp_fresh !inE. 
  move: (fresh_seq_nmem (finsupp p))=> /negP nFr.
  move=> eIn; apply/orP=> [[|]].
  - move=> /andP[] /[swap] /eqP ->.
    by move: esSub=> /fsubsetP /[apply].
  move: eIn=> /orP[/eqP->|eIn].   
  - rewrite /fs_ica /= /fs_rcov fsfun_dflt //; exact/negP.
  move: (irr (Sub e eIn)).
  by rewrite /fin_ica /sub_rel_down /= => ->.
Qed.

Lemma add_event_acyclic : supp_closed p -> 
  acyclic (fin_ica p) -> acyclic (fin_ica (lfspre_add_event l es p)).
Proof.
  move=> supcl acyc. 
  rewrite acyclicE; apply/andP; split.
  - apply/irreflexiveP/irreflexive_mono.
    + exact/fin_ica_mono.
    move=> /= e; apply/fs_ica_irrefl.
    + exact/add_event_supp_closed.
    + apply/add_event_irrefl=> //. 
      by move: acyc; rewrite acyclicE=> /andP[/irreflexiveP].
  apply/antisymmetricP/antisymmetric_mono. 
  - exact/fin_ca_mono.
  move=> /= e1 e2 /andP[].
  rewrite !add_event_fs_caE //.
  move=> /orP[|] + /orP[|].  
  - move=> /= /andP[? /eqP ?] /andP[? /eqP ?].
    apply/val_inj=> /=; congruence.
  - move=> /andP[in1 /eqP ->].
    move: (fresh_seq_nmem (finsupp p))=> /negP nFr.
    move=> /(supp_closed_ca supcl acyc)=> /orP[|].     
    + move: in1=> /[swap] /eqP<-. 
      by move=> /lfsp_dw_clos_subs.
    by move=> /andP[].    
  - move=> /[swap] /andP[in2 /eqP ->].  
    move: (fresh_seq_nmem (finsupp p))=> /negP nFr.
    move=> /(supp_closed_ca supcl acyc)=> /orP[|].     
    + move: in2=> /[swap] /eqP<-. 
      by move=> /lfsp_dw_clos_subs.
    by move=> /andP[].    
   by move=> ??; apply/val_inj/(fs_ca_antisym supcl acyc)/andP.
Qed.

End Theory.
End Theory.  

End AddEvent.


Module Export lFsPosetLTS.

Module Export Def.
Section Def.  
Context (E : identType) (L : choiceType) (bot : L).
Implicit Types (l : L) (es : {fset E}).
Implicit Types (p : lfsposet E L bot).

Definition lfsp_add_event l es p : lfsposet E L bot :=
  let e := lfsp_fresh p in
  let q := lfspre_add_event l es p in
  match (l != bot) && (es `<=` (finsupp p)) =P true with
  | ReflectF _  => lFsPoset.empty E L bot
  | ReflectT pf => 
    let: conj lD esSub := andP pf in
    let labD  := add_event_lab_defined es lD (lfsp_lab_defined p) in
    let supcl := add_event_supp_closed lD esSub (lfsp_supp_closed p) in
    let acyc  := add_event_acyclic lD esSub 
                   (lfsp_supp_closed p) 
                   (lfsp_acyclic p) 
    in
    lFsPoset (introT and3P (And3 labD supcl acyc))
  end.

End Def.
End Def.

(* TODO: there is a lot of copypaste from lFsPrePosetLTS ... *)
Module LTS.
Section LTS.
Context (E : identType) (L : choiceType) (bot : L).
Implicit Types (l : L) (es : {fset E}).
Implicit Types (p : lfsposet E L bot).

Definition ltrans l p q := 
  (l != bot) &&
  [exists es : fpowerset (finsupp p),
    q == lfsp_add_event l (val es) p 
  ]. 

Lemma enabledP l p :
  reflect (exists q, ltrans l p q) (l != bot).
Proof. 
  case: (l != bot)/idP=> lD; last first.
  - by constructor=> /= [[q]] /andP[].
  constructor; exists (lfsp_add_event l fset0 p). 
  apply/andP; split=> //.
  apply/existsP=> /=.
  have inPw: (fset0 \in fpowerset (finsupp p)).
  - rewrite fpowersetE; exact/fsub0set.
  pose es : fpowerset (finsupp p) := Sub fset0 inPw.
  by exists es.
Qed.
  
Definition mixin := 
  let S := lfsposet E L bot in
  @LTS.LTS.Mixin S L _ _ _ enabledP. 
Definition ltsType := 
  Eval hnf in let S := lfsposet E L bot in (LTSType S L mixin).

End LTS.

Arguments ltsType E L bot : clear implicits.

Module Export Exports.
Canonical ltsType.
End Exports.

End LTS.

Export LTS.Exports.

Module Export Theory.
Section Theory.  
Context (E : identType) (L : choiceType) (bot : L).
Implicit Types (l : L) (es : {fset E}).
Implicit Types (p q : lfsposet E L bot).
Implicit Types (tr : trace (LTS.ltsType E L bot)).

Import lPoset.Syntax.
Local Open Scope lts_scope.

Lemma lfsp_ltransP l p q :
  reflect (l != bot /\ exists2 es, 
             es `<=` finsupp p & 
             q = lfsp_add_event l es p)
          (p --[l]--> q).
Proof.
  rewrite /ltrans /= /LTS.ltrans.
  apply: (andPP idP). 
  apply/(equivP idP); split=> [/existsP|] /=.
  - move=> [es] /eqP->; exists (val es)=> //.
    rewrite -fpowersetE; exact/(valP es). 
  move=> [es] + ->; rewrite -fpowersetE.
  move=> inPw; apply/existsP=> /=.
  by exists (Sub es inPw).
Qed.

Lemma lfsp_add_eventE l es p : 
  l != bot ->
  (es `<=` finsupp p) ->
  ((finsupp (lfsp_add_event l es p) =  lfsp_fresh p |` finsupp p) *
  (fs_lab (lfsp_add_event l es p)   =1 fun e =>
    if e == lfsp_fresh p then l else fs_lab p e))                *
  ((fs_rcov (lfsp_add_event l es p) =1 fun e =>
    if e == lfsp_fresh p then es else fs_rcov p e)               *
  (fs_ica (lfsp_add_event l es p)   =2 fun e1 e2 => 
    (e1 \in es) && (e2 == lfsp_fresh p) || (fs_ica p e1 e2)))    *
  (fs_ca (lfsp_add_event l es p)    =2 fun e1 e2 =>
    (e1 \in lfsp_dw_clos p es) && (e2 == lfsp_fresh p) || (fs_ca p e1 e2)).
Proof.
  rewrite ?/lfsp_add_event; do ? case: eqP=> //=.
  move=> p0; case: (andP p0)=> //= *.
  rewrite add_event_finsuppE //; do ? split=> //>;
  rewrite (add_event_fs_labE,
           add_event_fs_icaE,
           add_event_fs_rcovE,
           add_event_fs_caE)//; case: (p)=> /=> /and3P[] //.
Qed.

Hint Resolve lfsp_supp_closed lfsp_acyclic : core.

Lemma invariant_operational : 
  @invariant L (LTS.ltsType E L bot) (@operational _ _ _).
Proof.
  move=> p q [l /lfsp_ltransP[? [? /[dup] ? /fsubsetP sub ->]]].
  move/operationalP=> o; apply/operationalP=>> //.
  rewrite lfsp_add_eventE // => /orP[|/o]; last exact.
  case/andP=> /lfsp_dw_closP[] // ? /supp_closed_ca/orP[]//.
  - by move/eqP=>-> /sub/fresh_seq_mem/ltW ? /eqP->.
  by case/andP=> /fresh_seq_mem/ltW ??? /eqP->.
Qed.

Lemma opetaional0 : operational (lFsPoset.empty E L bot).
Proof.
  rewrite /lFsPoset.empty /=.
  apply/forall2P=> ??; rewrite lFsPrePoset.fs_ca_empty.
  by apply/implyP=> /eqP->.
Qed.

Lemma lfsp_trace_fresh tr p:
  let emp := lFsPoset.empty E L bot in
  p = lst_state emp tr ->
  tr \in trace_lang emp -> lfsp_fresh p = iter (size tr) fresh (fresh \i0).
Proof.
  case: tr=> /= t it; rewrite /trace_lang /(_ \in _) /==>->.
  elim/last_ind: t it=> //= [_ _|].
  - rewrite /lfsp_fresh /lFsPrePoset.empty finsupp0 /fresh_seq /=.
    by rewrite /fresh encode0.
  case=> [[/=? s1 s2 ? /andP[/=/andP[st ?? /eqP]]]|].
  - move: st=> /[swap]<- /lfsp_ltransP /= [? [??->]].
    rewrite /lfsp_fresh lfsp_add_eventE /lfsp_fresh // finsupp0.
    suff<-: [:: fresh \i0] = fresh_seq fset0 |` fset0.
    - by rewrite /fresh_seq /= maxx0.
    by move=> ?; rewrite fsetU0 enum_fsetE enum_fset1 /= fresh_seq_nil.
  move=> st t [l s1 s2]; rewrite fst_state_rcons /=.
  move=> IHt; rewrite -rcons_cons is_trace_rcons=> /and3P[].
  case/lfsp_ltransP=> /= ? [?? eq'].
  move=> /[swap]; rewrite /adjoint /==> /eqP eq.
  move/IHt/[apply]; rewrite last_rcons size_rcons /= eq eq'.
  rewrite /lfsp_fresh lfsp_add_eventE //.
  by rewrite fresh_seq_add /lfsp_fresh max_l ?ltW ?fresh_lt // =>->.
Qed.

Lemma lfsp_trace_finsupp tr :
  let emp := lFsPoset.empty E L bot in
  let p := lst_state emp tr in
  tr \in trace_lang emp -> finsupp p = [fset e | e in nfresh (fresh \i0) (size tr)].
Proof.
  case: tr=> /= t it; rewrite /trace_lang /(_ \in _) /=.
  elim/last_ind: t it=> //= [_ _|].
  - by apply/fsetP=> ?; rewrite finsupp0 ?inE.
  case=> [[/=? s1 s2 ? /andP[/=/andP[st ?? /eqP]]]|].
  - move: st=> /[swap]<- /lfsp_ltransP /= [? [??->]].
    rewrite lfsp_add_eventE // /lfsp_fresh finsupp0.
    by apply/fsetP=> ?; rewrite ?inE /fresh_seq /= /(\i0) /fresh decodeK.
  move=> st t [l s1 s2]; rewrite fst_state_rcons /=.
  move=> IHt; rewrite -rcons_cons is_trace_rcons=> /and3P[].
  case/lfsp_ltransP=> /= ? [?? eq' /[dup] it ++ /[dup] ?].
  move=> /[swap]; rewrite /adjoint /src=> /eqP /= eq.
  move/IHt/[apply]; rewrite last_rcons /= eq=> /fsetP ine.
  apply/fsetP=> x; rewrite ?inE /= size_rcons nfreshSr mem_rcons ?inE.
  rewrite eq' lfsp_add_eventE // ?inE.
  move: (ine x); rewrite ?inE /==>->.
  suff->: lfsp_fresh s1 = iter (size t) fresh (fresh (fresh \i0)) by lattice.
  by rewrite (@lfsp_trace_fresh (Trace it)) //= -iterS iterSr.
Qed.

Lemma lfsp_trace_lab tr e : 
  let emp := lFsPoset.empty E L bot in 
  let p := lst_state emp tr in
  tr \in trace_lang emp -> fs_lab p e = nth bot (bot :: map lbl tr) (encode e).
Proof.
  case: tr=> /= t it; rewrite /trace_lang /(_ \in _) /=.
  elim/last_ind: t it=> //= [_ _|].
  - rewrite lFsPrePoset.fs_lab_empty. 
    by case: (encode _)=> //= ?; rewrite nth_nil.
  case=> [[/=? s1 s2 ? /andP[/=/andP[st ?? /eqP]]]|].
  - move: st=> /[swap]<- /lfsp_ltransP /= [? [??->]].
    rewrite lfsp_add_eventE // /lfsp_fresh finsupp0 fresh_seq_nil.
    rewrite lFsPrePoset.fs_lab_empty.
    case: (e =P \i1)=> [->|/eqP].
    - rewrite /(\i1) /fresh decodeK /= encode0 //.
    rewrite -(inj_eq encode_inj) encode1.
    case: (encode _)=> // -//= []//= ?.
    by rewrite nth_nil.
  move=> st t [l s1 s2]; rewrite fst_state_rcons /=.
  move=> IHt; rewrite -rcons_cons is_trace_rcons=> /and3P[].
  case/lfsp_ltransP=> /= ? [?? eq' /[dup] it ++ /[dup] ?].
  move=> /[swap]; rewrite /adjoint /src=> /eqP /= eq.
  move/IHt/[apply]; rewrite last_rcons /= eq.
  rewrite map_rcons /= -?rcons_cons nth_rcons /= size_map.
  rewrite eq' lfsp_add_eventE // (@lfsp_trace_fresh (Trace it)) // => ->.
  rewrite -(inj_eq encode_inj) /= ?(encode_fresh, encode_iter) encode0 add1n.
  case: ifP=> [/eqP->|]; case: ifP=> //=; first by rewrite ltnn.
  move=> *; rewrite nth_default //= size_map; lia.
Qed.

Lemma lfsp_lang_lin tr : 
  let emp := lFsPoset.empty E L bot in 
  let p := lst_state emp tr in
  tr \in trace_lang emp -> (map lbl tr) \in lin p.
Proof. 
  move=> emp p inTr; rewrite /lin inE /=.
  pose q := lFsPoset.of_seq E L bot (map lbl tr).
  have labsD : bot \notin (map lbl tr).
  - apply/mapP=> -[[/=> /(allP (trace_steps _))/[swap]<-]].
    by case/lfsp_ltransP=> /eqP.
  rewrite -/q /=; apply/bhom_leP; exists id; split; last by exists id.
  - move=> e; rewrite !fs_labE.
    rewrite lFsPoset.of_seq_valE ?lFsPrePoset.of_seq_labE //.
    by rewrite lfsp_trace_lab.
  move=> e1 e2; rewrite !fs_caE.
  rewrite lFsPoset.of_seq_valE ?lFsPrePoset.of_seq_fs_caE //.
  rewrite !lFsPrePoset.of_seq_finsupp //=.
  rewrite lfsp_trace_finsupp //= !in_fset /= !size_labels. 
  have op: operational p.
  - exact/(invarianl_trace_lan invariant_operational)/opetaional0.
  move=> in1 in2 /(fs_ca_ident_le)-/(_ _ _ op)-> //.
  by apply/orP; right; apply/and3P.
Qed.

End Theory.
End Theory.  

End lFsPosetLTS.
