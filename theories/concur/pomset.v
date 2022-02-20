From Coq Require Import Relations.
From RelationAlgebra Require Import lattice monoid rel boolean kat_tac.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat seq tuple.
From mathcomp Require Import eqtype choice order generic_quotient.
From mathcomp Require Import fintype finfun finset fingraph finmap zify.
From mathcomp.tarjan Require Import extra acyclic kosaraju acyclic_tsorted. 
From eventstruct Require Import utils rel relalg inhtype order ident lposet.
From eventstruct Require Import ilia.

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
Import Order.Theory.

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

Definition lfsp_events p : {fset E} := 
  [fset e in finsupp p | fs_lab p e != bot].

(* TODO: rename lfsp_size? *)
Definition fs_size p : nat := #|` lfsp_events p|.

Definition supp_closed p := 
  [forall e : finsupp p, forall e' : fs_rcov p (val e), 
    (val e \in lfsp_events p) && (val e' \in lfsp_events p) 
  ].

(* TODO: better name? *)
Definition operational p := 
  [forall e1 : lfsp_events p, forall e2 : lfsp_events p, 
    (fs_ca p (val e1) (val e2)) ==> (val e1 <=^i val e2)
  ].

Definition conseq_num p :=
  lfsp_events p == [fset e | e in nfresh \i0 (fs_size p)].

Definition lfsp_tseq p : seq E := 
  map val (tseq (rgraph (@fin_ica p))).

Definition lfsp_idx p : E -> nat := 
  fun e => index e (lfsp_tseq p). 

Definition lfsp_event p e0 : nat -> E := 
  fun n => nth e0 (lfsp_tseq p) n.

Definition lfsp_labels p : seq L := 
  map (fs_lab p) (lfsp_tseq p).

Definition lfsp_fresh p : E := 
  fresh_seq (lfsp_events p).

Definition lfsp_pideal p e : {fset E} := 
  [fset e' in (e |` lfsp_events p) | fs_ca p e' e].

(* TODO: unify with UpFinPOrder *)
Definition lfsp_dw_clos p es := 
  [seq e <- lfsp_events p | [exists e' : es, fs_ca p e (val e')]].

(* TODO: unify with UpFinPOrder *)
Definition lfsp_is_maximal p e := 
  [forall e' : lfsp_events p, (fs_ca p e (val e')) ==> (fs_ca p (val e') e)].

(* TODO: unify with UpFinPOrder *)
Definition lfsp_is_greatest p e := 
  [forall e' : lfsp_events p, fs_ca p (val e') e].

Definition lfsp_equiv_partition p r : {fset {fset E}} := 
  let part := equivalence_partition r [set: lfsp_events p] in
  [fset [fset (val e) | e : lfsp_events p & (e \in (P : {set _}))] | P in part].

(* TODO: move/restructure *)
Context (L' : eqType) (bot' : L').
Implicit Types (f : L -> L').

(* TODO: move to inhtype, make a type of inhtype morphisms? *)
Definition bot_preserving f := 
  f bot == bot'.

Definition finsupp_preserving p f := 
  [forall e : lfsp_events p, f (fs_lab p (val e)) != bot'].

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
Implicit Types (p q : lfspreposet E L bot) (ls : seq L).

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

(* Lemma lfsp_events_finsupp p :  *)
(*   lfsp_events p `<=` finsupp p *)

Lemma supp_closedP p : 
  reflect (forall e1 e2, fs_ica p e1 e2 -> 
            (e1 \in lfsp_events p) * (e2 \in lfsp_events p))
          (supp_closed p).
Proof. 
  rewrite /supp_closed /fs_ica.
  apply/(equivP (forallPP _)). 
  - move=> ?; exact/forallP.
  split=> /=; last first.
  - move=> ica_supp; case=> e2 in_supp /=; case=> e1 in1 /=.
    by move: (ica_supp e1 e2 in1)=> [-> ->].
  move=> all_supp e1 e2 in1 /=.
  case: (in_fsetP (finsupp p) e2)=> [e2'|]; last first.
  - move: in1=> + /fsfun_dflt. 
    by rewrite /fs_rcov=> /[swap] -> /= //.
  move: in1=> /[swap] -> in1.
  move: (all_supp e2' (Sub e1 in1))=> /=. 
  case: (val e2' \in lfsp_events p)=> /=.
  move=> /implyP.  
  - move: (all_supp e2')=> /fsubsetP /[swap] /= <- /[apply] ->. *)
  by move=> /fsfun_dflt -> //.
Qed.

Lemma fs_sca_def p e1 e2 : 
  fs_sca p e1 e2 = (e2 != e1) && (fs_ca p e1 e2).
Proof. done. Qed.

Lemma fs_ca_scaE p e1 e2 : 
  fs_ca p e1 e2 = (e1 == e2) || (fs_sca p e1 e2).
Proof.
  rewrite /fs_sca orb_andr eq_sym orbN andTb. 
  apply/esym; rewrite orb_idl //.
  move=> /eqP->; rewrite /fs_ca /=. 
  by apply/orP; left.
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

Lemma fs_ca_refl p : 
  reflexive (fs_ca p). 
Proof. by move=> x; rewrite /fs_ca /=; apply/orP; left. Qed.

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

Lemma fs_ca_trans p : 
  supp_closed p -> transitive (fs_ca p). 
Proof. 
  move=> supcl y x z.
  move=> /(fs_caP _ _ supcl) ca_xy.
  move=> /(fs_caP _ _ supcl) ca_yz.
  apply/(fs_caP _ _ supcl). 
  apply/rt_trans; [exact/ca_xy | exact/ca_yz].
Qed. 

Lemma fin_ica_acyclic p : 
  irreflexive (fs_ica p) -> antisymmetric (fs_ca p) -> acyclic (fin_ica p).
Proof. 
  move=> irrefl asym.
  rewrite acyclicE; apply/andP; split.
  - apply/irreflexiveP/irreflexive_mono; first exact/fin_ica_mono.
    by move=> ? /=.
  apply/antisymmetricP/antisymmetric_mono; first exact/fin_ca_mono. 
  move=> /= x y /andP[??].
  by apply/val_inj/asym/andP.
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

Lemma fs_ca_nsupp p e1 e2 : supp_closed p -> acyclic (fin_ica p) -> 
  ((e1 \notin finsupp p) || (e2 \notin finsupp p)) -> fs_ca p e1 e2 -> e1 = e2.
Proof. 
  move=> supcl acyc /[swap]. 
  move=> /(supp_closed_ca supcl acyc) /orP[/eqP->|] //.
  by move=> /andP[??] /orP[|] /negP.
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

Lemma lfsp_dw_clos_subs p es : 
  {subset (lfsp_dw_clos p es) <= finsupp p}.
Proof. by move=> e; rewrite mem_filter=> /andP[]. Qed.

Lemma lfsp_pidealP p e e' : supp_closed p -> acyclic (fin_ica p) -> 
  e' \in (lfsp_pideal p e) = (fs_ca p e' e).
Proof. 
  move=> supcl acyc.
  rewrite /lfsp_pideal !inE; apply/andb_idl.
  move=> /(supp_closed_ca supcl acyc).
  by move=> /orP[/eqP->|/andP[->]]; rewrite ?eq_refl. 
Qed.
   
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

(* TODO: do we need acyclic precondition? *)
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

Lemma operational_sca p : 
  supp_closed p -> acyclic (fin_ica p) -> operational p ->
    subrel (fs_sca p) (<^i%O).
Proof.
  move/operationalP/[apply]/[apply] => sb> /andP[/[swap]/sb].
  by rewrite lt_neqAle eq_sym=>->->. 
Qed.

Lemma fs_ca_ident_le p :
  supp_closed p -> acyclic (fin_ica p) -> operational p ->
    subrel (fs_ca p) <=^i%O.
Proof. move=>?? /operationalP; exact. Qed.

Lemma fs_ica_fin_icaE p : 
  supp_closed p -> fs_ica p =2 sub_rel_lift (fin_ica p).
Proof.
  move=> sc>; rewrite /fin_ica sub_rel_lift_downK=> //=>.
  by case/(supp_closedP _ sc)=> /=->.
Qed.

Lemma conseq_num_mem p e : 
  conseq_num p -> (e \in finsupp p) = (encode e < fs_size p)%N.
Proof. 
  move=> /eqP->; rewrite in_fset /=.
  by rewrite in_nfresh encode0 addn0 /=. 
Qed.

End Theory.

Section TheoryAux.
Context (E : identType) (L1 : eqType) (L2 : eqType) (bot1 : L1) (bot2 : L2).
Implicit Types (p : lfspreposet E L1 bot1).
Implicit Types (q : lfspreposet E L2 bot2).

Lemma fs_ca_ica_eq p q : supp_closed p -> 
  finsupp p = finsupp q -> fs_ica p =2 fs_ica q -> fs_ca p =2 fs_ca q.
Proof. 
  move=> supclp eqsupp eq_ica e1 e2. 
  have supclq : supp_closed q.
  - apply/supp_closedP=> {}e1 {}e2.
    rewrite -eqsupp -eq_ica.
    by apply/supp_closedP.
  have eq_ica': (fs_ica p : hrel E E) ≡ fs_ica q.
  - by move=> ?? /=; rewrite eq_ica.
  apply/idP/idP.
  - move=> /(fs_caP _ _ supclp)/clos_rt_str.
    rewrite !(str_weq eq_ica')=> ?. 
    by apply/(fs_caP _ _ supclq)/clos_rt_str.
  move=> /(fs_caP _ _ supclq)/clos_rt_str.
  rewrite -(str_weq eq_ica')=> ?. 
  by apply/(fs_caP _ _ supclp)/clos_rt_str.    
Qed.

End TheoryAux.

End Theory.

Section Build.
Context (E : identType) (L : eqType) (bot : L). 
Context (fE : {fset E}).
Implicit Types (p : lfspreposet E L bot).
Implicit Types (lab : fE -> L) (ica : rel fE) (ca : rel E).

Definition build lab ica : lfspreposet E L bot := 
  let rcov e := [fsetval e' in rgraph [rel x y | ica y x] e] in
  [fsfun e => (lab e, rcov e)].

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
  move=> acyc; apply/fin_ica_acyclic. 
  - move=> e; rewrite build_ica /sub_rel_lift /=.
    case: insubP=> // e' ??; exact/acyc_irrefl.
  move=> /= x y /andP[].
  pose supcl := supp_closed_build.
  move=> /(fs_caP _ _ supcl)/clos_rt_str + /(fs_caP _ _ supcl)/clos_rt_str.
  have eq_ica: (fs_ica (build lab ica) : hrel E E) ≡ sub_rel_lift ica.
  - by move=> ?? /=; rewrite build_ica.
  rewrite !(str_weq eq_ica) !sub_rel_lift_connect. 
  move=> [->|] // + [->|] //.
  rewrite /sub_rel_lift /=.
  case: insubP=> //= x' ? <-; case: insubP=> //= y' ? <-.
  move=> ??; suff->: x' = y' => //.
  by apply/(acyc_antisym acyc)/andP.
Qed.  

End Build.

Section BuildCov.
Context (E : identType) (L : eqType) (bot : L). 
Context (fE : {fset E}).
Implicit Types (p : lfspreposet E L bot).
Implicit Types (lab : fE -> L) (ica : rel fE) (ca : rel E).

Definition build_cov lab ca : lfspreposet E L bot := 
  let sca : rel E := (fun x y => (y != x) && (ca x y)) in
  let ica : rel fE := cov (relpre val sca) in
  @build E L bot fE lab ica.

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
  move: in1 in2; case: _ / (esym (@build_finsupp E L bot fE lab ica labD))=> *.
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

(* TODO: generalize *)
Lemma build_cov_acyclic_sca :
  let D := finsupp (build_cov lab ca) in
  acyclic (relpre val sca : rel D).
Proof.
  apply/acyclicP; split=> [[/= ??]|]; first by rewrite /sca eq_refl.
  apply/preacyclicP=> ?? /andP[].
  rewrite !build_cov_connect_sca !build_cov_connect_ca /= => ??.
  by apply/val_inj/ca_anti/andP.
Qed.

(* TODO: use build_acyclic? *)
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

(* TODO: rename? *)
Lemma build_cov_ca_wf : subrel ca (mem fE × mem fE : {dhrel E & E})^? -> 
  fs_ca (build_cov lab ca) =2 ca.
Proof. 
  move=> sub e1 e2; rewrite build_cov_ca.
  apply/idP/idP=> [/orP[|]|].
  - move=> /eqP->; exact/ca_refl.
  - by move=> /and3P[].
  move=> /[dup] /sub /= /orP[|]. 
  - by move=> /eqP-> ?; apply/orP; left. 
  by move=> /andP[-> ->] ->; rewrite orbT.
Qed.

End BuildCov.

Section Empty.
Context (E : identType) (L : eqType) (bot : L). 
Implicit Types (p : lfspreposet E L bot).

Definition empty : lfspreposet E L bot := [fsfun].

Lemma finsupp_empty : 
  finsupp empty = fset0.
Proof. exact/finsupp0. Qed.

Lemma fs_size_empty : 
  fs_size empty = 0%N.
Proof. by rewrite /fs_size finsupp_empty. Qed.

Lemma empty_eqP p : 
  reflect (p = empty) (fs_size p == 0%N).
Proof.
  apply/(equivP idP); split=> [|->]; last first. 
  - by rewrite fs_size_empty. 
  rewrite /fs_size=> /eqP/cardfs0_eq fE; apply/fsfunP=> e /=. 
  by rewrite /empty fsfun0E !fsfun_dflt // fE inE.
Qed.

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

Lemma empty_operational : 
  operational empty.
Proof.
  apply/forall2P=> ??; rewrite fs_ca_empty.
  by apply/implyP=> /eqP->.
Qed.

Lemma empty_conseq_num : 
  conseq_num empty.
Proof.
  rewrite /conseq_num finsupp_empty. 
  apply/eqP/fsetP=> e /=.
  rewrite in_fset /= inE in_nfresh encode0 addn0 /=.
  by rewrite fs_size_empty ltn0. 
Qed.

Lemma empty_total : 
  total (fin_ca empty).
Proof.
  case=> x xP; exfalso.
  by move: xP; rewrite finsupp0. 
Qed.

End Empty.

Arguments empty E L bot : clear implicits.

Section OfSeq.
Context (E : identType) (L : eqType) (bot : L). 
Implicit Types (p : lfspreposet E L bot).
Implicit Types (ls : seq L).

Definition of_seq ls := 
  let fE  := [fset e | e in nfresh \i0 (size ls)] in 
  let lab := fun e : fE => (nth bot ls (encode (val e))) in
  let ca  := fun e1 e2 : E => e1 <=^i e2 in
  @build_cov E L bot fE lab ca.

Variable (ls : seq L).
Hypothesis (lsD : bot \notin ls).

Lemma of_seq_nth_defined : 
  forall (e : [fset e | e in nfresh \i0 (size ls)]),
    nth bot ls (@encode E (val e)) != bot.
Proof.
  move: lsD=> /negP nbl [/= ?].
  rewrite ?inE /=; encodify=> ?.
  apply/negP; move: nbl=> /[swap]/eqP<-.
  apply; apply/mem_nth; lia.
Qed.

Lemma of_seq_finsupp : 
  finsupp (of_seq ls) = [fset e | e in nfresh \i0 (size ls)].
Proof. rewrite build_finsupp //; exact/of_seq_nth_defined. Qed.

(* TODO: derie from conseq_num *)
Lemma of_seq_fresh :
  lfsp_fresh (of_seq ls) = iter (size ls) fresh \i0.
Proof.
  rewrite /lfsp_fresh /fresh_seq of_seq_finsupp.
  case: (boolP (size ls == 0%N))=> [|neq].
  - rewrite size_eq0=> /eqP-> /=.
    by rewrite nfresh0 fset_nil /=.
  rewrite -fresh_seq_nfresh //.
  apply/max_set_eq; first exact/le0x.
  by apply/eq_mem_map=> x; rewrite !inE. 
Qed.

Lemma of_seq_size : 
  fs_size (of_seq ls) = size ls.
Proof.
  rewrite /fs_size of_seq_finsupp card_fseq undup_id ?size_nfresh //.
  exact/lt_sorted_uniq/nfresh_sorted.
Qed.

Lemma of_seq_conseq_num : 
  conseq_num (of_seq ls).
Proof. by rewrite /conseq_num of_seq_finsupp of_seq_size. Qed.

Lemma of_seq_labE e : 
  fs_lab (of_seq ls) e = nth bot ls (encode e).
Proof.
  rewrite /of_seq build_lab /= /sub_lift.
  case: insubP=> /= [?? ->|] //.
  rewrite ?inE /==> ?; rewrite nth_default; ilia.
Qed.

Lemma of_seq_fin_caE : 
  fin_ca (of_seq ls) =2 relpre val [rel e1 e2 | e1 <=^i e2]. 
Proof. 
  apply/build_cov_fin_ca=> // [? ||]; last first.
  - exact/le_trans.
  - exact/le_anti.
  by rewrite of_seq_nth_defined.
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

Lemma of_seq_fin_icaE e1 e2 : 
  fin_ica (of_seq ls) e1 e2 = (fresh (val e1) == val e2).
Proof.
  rewrite /of_seq build_cov_fin_ica; first last.
  - case=> /= ?; rewrite ?inE /==> ?.
    apply/eqP; move: lsD=> /[swap]<-.
    rewrite mem_nth=> //; ilia.
  apply/covP/eqP=> /=; case: e1 e2=> /= e1 i1 [/= e2 i2].
  - case=> _ /andP[?? nex]. 
    case: (fresh e1 =P e2)=> // /eqP ?; case: nex.
    move: i1 i2; rewrite of_seq_finsupp ?inE /==> ??.
    have IN: (fresh e1 \in [fset e | e in nfresh \i0 (size ls)]).
    - rewrite ?inE /=; ilia.
    exists [`IN] => /=; ilia.
  split=> [/(congr1 val)||[[/= ? _]]]; ilia.
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

Hint Resolve of_seq_supp_closed : core. 

Lemma of_seq_fs_icaE e1 e2 : 
  fs_ica (of_seq ls) e1 e2 = 
    [&& fresh e1 == e2
      , e1 \in finsupp (of_seq ls)
      & e2 \in finsupp (of_seq ls)
    ].
Proof.
  rewrite fs_ica_fin_icaE // /sub_rel_lift /=. 
  case: insubP=> [? ->|/negbTE->]; last lattice.
  case: insubP=> [? ->|/negbTE-> //]; last by rewrite andbC.
  rewrite of_seq_fin_icaE=>->->; lattice.
Qed.

Lemma of_seq_acyclic : 
  acyclic (fin_ica (of_seq ls)).
Proof.
  apply/build_cov_acyclic=> [? |||]; last first.
  - exact/le_trans.
  - exact/le_anti.
  - exact/le_refl.
  by rewrite of_seq_nth_defined.
Qed.

Lemma of_seq_operational : 
  operational (of_seq ls). 
Proof. 
  apply/operationalP.
  - exact/of_seq_supp_closed.
  - exact/of_seq_acyclic.
  move=> e1 e2; rewrite of_seq_fs_caE.
  by move=> /orP[/eqP->|/and3P[]].
Qed.

Lemma of_seq_total : 
  total (fin_ca (of_seq ls)).   
Proof. move=> e1 e2; rewrite !of_seq_fin_caE /=; exact/le_total. Qed.

End OfSeq.

Arguments of_seq E L bot : clear implicits.

Section InterRel.
Context (E : identType) (L : eqType) (bot : L). 
Implicit Types (r : rel E).
Implicit Types (p : lfspreposet E L bot).

(* TODO: perhaps, we should define intersection for preorders only?
 *   Then we would have homogeneous binary operation, 
 *   and all the invariants in-place. 
 *   For that, however, we need to change hierarchy to something like:
 *  
 *                             /-- lfsposet
 *   lfsrepr <-- lfspreposet <-
 *                             \-- lfsequiv
 *            
 *)
Definition inter_rel r p := 
  @build_cov E L bot _ (fin_lab p) (r ⊓ (fs_ca p)).

Lemma inter_rel_finsupp r p : 
  lab_defined p -> finsupp (inter_rel r p) = finsupp p.
Proof. by move=> ?; rewrite build_finsupp //; apply/forallP. Qed.

Lemma inter_rel_labE r p : 
  fs_lab (inter_rel r p) =1 fs_lab p.
Proof.
  move=> e; rewrite /inter_rel build_lab. 
  case: (e \in finsupp p)/idP=> [eIn | enIn].
  - by rewrite sub_liftT. 
  rewrite sub_liftF // /fs_lab fsfun_dflt //. 
  exact/negP.    
Qed.

Lemma inter_rel_lab_defined r p : 
  lab_defined p -> lab_defined (inter_rel r p).
Proof. move=> labD; apply/lab_defined_build; exact/forallP. Qed.

Lemma inter_rel_supp_closed r p : 
  lab_defined p -> supp_closed p -> supp_closed (inter_rel r p).
Proof.
  move=> labD supcl; apply/supp_closedP=>>.
  rewrite build_ica build_finsupp //; last first. 
  - move=> ?; rewrite /fin_lab; apply/lab_definedP=> //; exact/valP. 
  by move=> /sub_rel_liftP[[>[[>[? /= <- <-]]]]].
Qed.

Variables (r : rel E) (p : lfspreposet E L bot).
Hypothesis (refl  : reflexive r).
Hypothesis (trans : transitive r).
Hypothesis (labD  : lab_defined p).
Hypothesis (supcl : supp_closed p).
Hypothesis (acyc  : acyclic (fin_ica p)).

(* TODO: prove for lfposet? *)
Lemma inter_rel_acyclic : 
  acyclic (fin_ica (inter_rel r p)).
Proof. 
  apply/build_cov_acyclic.
  - move=> e; apply/lab_definedP=> //; exact/valP.
  - apply/refl_cap=> //; exact/fs_ca_refl.
  - under eq_antisym do rewrite capC.
    exact/antisym_cap/fs_ca_antisym. 
  apply/trans_cap=> //; exact/fs_ca_trans.
Qed.

Lemma inter_rel_ca : 
  fs_ca (inter_rel r p) =2 r ⊓ (fs_ca p).
Proof. 
  rewrite /inter_rel=> e1 e2.
  rewrite build_cov_ca_wf //.
  (* TODO: remove copy-paste! *)
  - move=> e; apply/lab_definedP=> //; exact/valP.
  - apply/refl_cap=> //; exact/fs_ca_refl.
  - under eq_antisym do rewrite capC.
    exact/antisym_cap/fs_ca_antisym. 
  - apply/trans_cap=> //; exact/fs_ca_trans.
  move=> {}e1 {}e2 /andP[_] ca12. 
  by apply/supp_closed_ca. 
Qed.

End InterRel.

Section Restrict.
Context (E : identType) (L : eqType) (bot : L).
Implicit Types (P : pred E).
Implicit Types (p : lfspreposet E L bot).

Definition restrict P p : lfspreposet E L bot :=
  (* TODO: there should be a simpler solution... *)
  let fE  := [fset e in finsupp p | P e] in
  let lab := (fun e : fE => fs_lab p (val e)) in
  let ca  := (eq_op ⊔ (P × P)) ⊓ (fs_ca p) in
  @build_cov E L bot _ lab ca.

Variables (P : pred E) (p : lfspreposet E L bot).
Hypothesis (labD  : lab_defined p).
Hypothesis (supcl : supp_closed p).
Hypothesis (acyc  : acyclic (fin_ica p)).

Lemma restrict_finsupp : 
  finsupp (restrict P p) = [fset e in finsupp p | P e].
Proof. 
  apply/fsetP=> e.
  rewrite mem_finsupp fsfun_ffun.
  case: insubP=> /= [e' /[swap] /= <- eIn|/negbTE-> /[! eqxx] //] /=.
  rewrite xpair_eqE negb_and eIn. 
  apply/idP/orP; left.
  apply/lab_definedP=> //.
  apply/(fsubsetP _ _ eIn).
  exact/fset_sub.
Qed.

Lemma restrict_lab e : 
  fs_lab (restrict P p) e = if P e then fs_lab p e else bot.
Proof. 
  rewrite /restrict /build_cov build_lab /sub_lift /=.
  case: insubP; rewrite !inE=> //=. 
  - by move=> ? /andP[? ->] ->.
  rewrite negb_and=> /orP[nIn|/negPf->] //=. 
  case: ifP=> //.
  by rewrite /fs_lab fsfun_dflt.
Qed.

Lemma restrict_lab_defined : 
  lab_defined (restrict P p).
Proof. 
  apply/lab_definedP=> e.
  rewrite restrict_finsupp restrict_lab !inE.
  move=> /= /andP[eIn ->].
  exact/lab_definedP.
Qed.

Lemma restrict_supp_closed : 
  supp_closed (restrict P p).
Proof. 
  apply/supp_closedP=> e1 e2.
  rewrite restrict_finsupp=> /=. 
  rewrite /restrict /build_cov build_ica /sub_rel_lift /=.
  by do 2 (case: insubP=> //= ? /[swap] <-). 
Qed.

Lemma restrict_ca e1 e2 : 
  fs_ca (restrict P p) e1 e2 = (e1 == e2) || [&& P e1, P e2 & fs_ca p e1 e2].
Proof.
  rewrite build_cov_ca_wf=> //=.  
  (* TODO: remove copypaste! *)
  - rewrite andb_orl andbA. 
    apply/orb_id2r=> _; apply/andb_idr.
    move=> /eqP->; exact/fs_ca_refl.
  - move=> e; apply/lab_definedP=> //.
    apply/(fsubsetP _ _ (valP e)).
    exact/fset_sub.
  - apply/refl_cap=> //; last exact/fs_ca_refl.
    by move=> ? /=; rewrite eq_refl.
  - under eq_antisym do rewrite capC.
    exact/antisym_cap/fs_ca_antisym. 
  - apply/trans_cap=> // [??? |] /=; last exact/fs_ca_trans.
    move=> /orP[/eqP->|/andP[??]] //. 
    move=> /orP[/eqP<-|/andP[??]] //. 
    1-2: by apply/orP; right; apply/andP.
  move=> /= {}e1 {}e2; rewrite /dhrel_one /=.
  move=> /andP[/orP[->|/andP[??]]] //.
  move=> /(supp_closed_ca supcl acyc) /orP[->|/andP[??]] //.
  by rewrite !inE; apply/orP; right; apply/andP; split; apply/andP.
Qed.

Lemma restrict_acyclic :
  acyclic (fin_ica (restrict P p)).
Proof.
  apply/fin_ica_acyclic.
  - apply/fs_ica_irrefl; first exact/restrict_supp_closed.
    move=> x; rewrite /restrict build_cov_fin_ica; first exact/cov_irrefl.
    move=> e; apply/(lab_definedP _ labD). 
    by move: (valP e); rewrite !inE=> /andP[].
  move=> e1 e2; rewrite !restrict_ca //.
  move=> /andP[] /orP[/eqP->|] // + /orP[/eqP->|] //.
  move=> /and3P[???] /and3P[???].
  exact/(fs_ca_antisym supcl acyc)/andP. 
Qed.

End Restrict.


Section Relabel.
Context (E : identType) (L1 : eqType) (L2 : eqType) (bot1 : L1) (bot2 : L2). 
Implicit Types (f : L1 -> L2).
Implicit Types (p : lfspreposet E L1 bot1).

Definition relabel f p : lfspreposet E L2 bot2 :=
  [fsfun e in finsupp p => (f (fs_lab p e), fs_rcov p e)].

Variables (f : L1 -> L2) (p : lfspreposet E L1 bot1).
(* TODO: use inhtype to get rid of explicit bot arguments... *)
Hypothesis (fbot : bot_preserving bot1 bot2 f).
Hypothesis (fsupp : finsupp_preserving bot2 p f).

(* TODO: refactor this precondition? *)
(* Hypothesis (flabD : forall e, let l := fs_lab p e in (l == bot1) = (f l == bot2)). *)
(* Hypothesis (labD : lab_defined (relabel f p)). *)

Lemma relabel_finsupp : 
  finsupp (relabel f p) = finsupp p.
Proof. 
  apply/fsetP=> e.
  rewrite mem_finsupp fsfun_ffun.
  case: insubP=> /= [e' /[swap] /= <- eIn|/negbTE-> /[! eqxx] //] /=.
  rewrite xpair_eqE negb_and eIn. 
  apply/idP/orP; left.
  exact/(forallP fsupp). 
Qed.

Lemma relabel_lab : 
  fs_lab (relabel f p) =1 (f \o fs_lab p).
Proof. 
  rewrite /relabel /fs_lab=> e /=.
  rewrite fsfun_fun; case: ifP=> //=.
  move=> /negP nIn /=; apply/esym/eqP.
  rewrite fsfun_dflt ?fbot //=. 
  exact/negP.
Qed.

Lemma relabel_ica : 
  fs_ica (relabel f p) =2 fs_ica p.
Proof.
  rewrite /fs_ica /relabel=> e1 e2 /=.
  rewrite /fs_rcov fsfun_fun. 
  case: ifP=> //= /negP ?.
  rewrite fsfun_dflt ?inE //; exact/negP.
Qed.

Lemma relabel_lab_defined : 
  lab_defined (relabel f p).
Proof. 
  apply/lab_definedP=> e.
  rewrite relabel_finsupp relabel_lab=> eIn /=. 
  have->: e = val (Sub e eIn : finsupp p) by done.
  exact/(forallP fsupp). 
Qed.

Lemma relabel_supp_closed : 
  supp_closed p -> supp_closed (relabel f p).
Proof. 
  move=> supcl; apply/supp_closedP=> e1 e2.
  rewrite relabel_finsupp relabel_ica=> ica.
  by apply/supp_closedP. 
Qed.

Lemma relabel_ca :
  supp_closed p -> fs_ca (relabel f p) =2 fs_ca p.
Proof.
  move=> supcl; apply/fs_ca_ica_eq.
  - exact/relabel_supp_closed.
  - by rewrite relabel_finsupp.  
  exact/relabel_ica.
Qed.

Lemma relabel_acyclic : 
  supp_closed p -> acyclic (fin_ica p) -> acyclic (fin_ica (relabel f p)).
Proof.
  move=> suplc acyc; apply/fin_ica_acyclic.
  - move=> e; rewrite relabel_ica.
    apply/fs_ica_irrefl=> //. 
    exact/acyc_irrefl.
  move=> e1 e2; rewrite !relabel_ca //.
  exact/fs_ca_antisym. 
Qed.

End Relabel.

End lFsPrePoset.

Export lFsPrePoset.Def.
Export lFsPrePoset.Theory.


Module lFsPoset.

Module Export Def.
Section Def. 
Context (E : identType) (L : eqType).
Variable (bot : L).

Structure lfsposet : Type := mklFsPoset {
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

Section BuildCov.
Context (E : identType) (L : eqType) (bot : L). 
Context (fE : {fset E}).
Implicit Types (p : lfsposet E L bot).
Implicit Types (lab : fE -> L) (ica : rel fE) (ca : rel E).

Variables (lab : fE -> L) (ca : rel E).
Hypothesis labD : forall e, lab e != bot.
Hypothesis ca_refl  : reflexive ca.
Hypothesis ca_anti  : antisymmetric ca.
Hypothesis ca_trans : transitive ca.

Lemma build_covP : 
  let p := lFsPrePoset.build_cov bot lab ca in
  [&& lab_defined p,
      supp_closed p &
      acyclic (fin_ica p)].
Proof.
  apply/and3P; split.
  - apply/lab_definedP=>>.
    rewrite lFsPrePoset.build_lab lFsPrePoset.build_finsupp // => ?.
    by rewrite sub_liftT.
  - apply/supp_closedP=>>.
    rewrite  lFsPrePoset.build_ica lFsPrePoset.build_finsupp /sub_rel_lift //=.
    by do 2 case: insubP=> //.
  exact/lFsPrePoset.build_cov_acyclic.
Qed.

Definition build_cov := mklFsPoset build_covP.

End BuildCov.


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
  mklFsPoset emptyP.

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
  exact/lFsPrePoset.of_seq_acyclic.
Qed.

Definition of_seq ls : lfsposet E L bot := 
  if bot \notin ls =P true is ReflectT nbl then
    mklFsPoset (of_seqP nbl)
  else empty E L bot.

Lemma of_seq_valE ls : 
  val (of_seq ls) = 
    if (bot \notin ls) then 
      lFsPrePoset.of_seq E L bot ls
    else 
      lFsPrePoset.empty E L bot.
Proof. by case: ifP; rewrite /of_seq; case: eqP=> //= ->. Qed.

Lemma of_seq_size ls : 
  fs_size (of_seq ls) = if (bot \notin ls) then size ls else 0%N.
Proof. 
  rewrite of_seq_valE; case: ifP=> ?. 
  - by rewrite lFsPrePoset.of_seq_size. 
  exact/eqP/lFsPrePoset.empty_eqP.
Qed.

Lemma of_seq_labE ls e :
  fs_lab (of_seq ls) e = if (bot \notin ls) then nth bot ls (encode e) else bot.
Proof. 
  rewrite of_seq_valE; case: ifP=> ?.
  - exact/lFsPrePoset.of_seq_labE.
  exact/lFsPrePoset.fs_lab_empty. 
Qed.

Lemma of_seq_caE ls e1 e2 :
  fs_ca (of_seq ls) e1 e2 = 
    (e1 == e2) ||
    [&& e1 <=^i e2
      , e1 \in finsupp (of_seq ls)
      , e2 \in finsupp (of_seq ls)
      & bot \notin ls
    ].
Proof. 
  rewrite of_seq_valE; case: ifP=> ?.
  - by rewrite andbT lFsPrePoset.of_seq_fs_caE.
  by rewrite !andbF orbF lFsPrePoset.fs_ca_empty. 
Qed.

Lemma of_seq_operational ls : 
  operational (of_seq ls).
Proof. 
  rewrite of_seq_valE; case: ifP=> ?.
  - exact/lFsPrePoset.of_seq_operational. 
  exact/lFsPrePoset.empty_operational. 
Qed.

Lemma of_seq_conseq_num ls : 
   (conseq_num (of_seq ls)).
Proof. 
  rewrite of_seq_valE; case: ifP=> ?.
  - exact/lFsPrePoset.of_seq_conseq_num. 
  exact/lFsPrePoset.empty_conseq_num. 
Qed.

Lemma of_seq_total ls : 
  total (fin_ca (of_seq ls)).
Proof. 
  rewrite of_seq_valE; case: ifP=> ?.
  - exact/lFsPrePoset.of_seq_total. 
  exact/lFsPrePoset.empty_total. 
Qed.

End OfSeq.

(* TODO: move to pomset_lts.v (by analogy with add_event)? *)
Section DeleteMax.
Context (E : identType) (L : eqType) (bot : L).
Context (p : lfsposet E L bot) (x : E).

(* TODO: rename remove_event (by analogy with add_event)? *)
Definition delete_pre := [fsfun p without x].

(* TODO: split to lFsPrePoset & lFsPoset? 
 *   Current definition of delete_pre is defined on `lfsposet`
 *   and thus saves us from tedious preconditions 
 *   (lab_defined, supp_closed, etc). 
 *   But on the other hand, it makes it non-applicable to `lfspreposet`
 *   (i.e. cyclic graphs).
 *)

Section DeletePre.
(* TODO: make `fs_maximal` definition *)
Hypothesis x_max : [forall y : finsupp p, ~~ fs_ica p x (val y)].

(* TODO: move to lFsPoset.Theory *)
Lemma x_maximal : forall y, ~ fs_ica p x y.
Proof.
  move=> ? /[dup] /(supp_closedP _ (lfsp_supp_closed _))[_ i].
  by move/forallP/(_ [`i])/negP: x_max.
Qed.

Lemma delete_finsupp : finsupp delete_pre = finsupp p `\ x.
Proof. exact/finsupp_without. Qed.

Lemma delete_fs_lab : 
  fs_lab delete_pre =1 fun e => if e == x then bot else fs_lab p e.
Proof. move=>>; rewrite /fs_lab fsfun_withE; by case: ifP. Qed.

Lemma delete_fs_ica : 
  fs_ica delete_pre =2 fun e1 e2 => if e2 != x then fs_ica p e1 e2 else false.
Proof. move=>>; rewrite /fs_ica /= /fs_rcov fsfun_withE; by case: ifP. Qed.

Lemma delete_supp_closed : supp_closed delete_pre.
Proof.
  apply/supp_closedP=> e1 e2.
  move/supp_closedP/(_ e1 e2): (lfsp_supp_closed p).
  rewrite delete_fs_ica delete_finsupp ?inE; case: ifP=> //= _.
  by move=> sc /[dup]/sc [->->]; case: (_ =P _)=> //->/x_maximal.
Qed.

Lemma delete_fs_ca : 
  fs_ca delete_pre =2 fun e1 e2 => if e2 != x then fs_ca p e1 e2 else e1 == e2.
Proof.
  move=>>; apply/(fs_caP _ _ delete_supp_closed)/idP.
  - move/clos_rt_rtn1_iff; elim=> [|y ? + _].
    - case: (_ =P _)=> //= _; exact/fs_ca_refl.
    rewrite delete_fs_ica; case: ifP=> // ?.
    case: (_ =P _)=> //= [-> /x_maximal //|? fi ?].
    apply/(fs_caP _ _ (lfsp_supp_closed p))/clos_rt_rtn1_iff.
    econstructor; first exact/fi.
    exact/clos_rt_rtn1_iff/(fs_caP _ _ (lfsp_supp_closed p)).
  case: (_ =P _)=> /= [->/eqP->|/[swap]]; first by constructor.
  move/(fs_caP _ _ (lfsp_supp_closed p))/clos_rt_rtn1_iff.
  rewrite clos_rt_rtn1_iff.
  elim=> [|y ? + _]; first by constructor.
  case: (y =P x)=> [->/x_maximal //| nyx ? /(_ nyx) fi ?].
  econstructor; last exact/fi; rewrite delete_fs_ica; by case (_ =P _).
Qed.

Lemma delete_lab_defined : lab_defined delete_pre.
Proof.
  apply/lab_definedP=>>. 
  rewrite delete_finsupp delete_fs_lab ?inE; case: ifP=> //= _.
  exact/lab_definedP/lfsp_lab_defined.
Qed.

Lemma delete_acyclic : acyclic (fin_ica delete_pre).
Proof.
  apply/fin_ica_acyclic=>>. 
  - rewrite delete_fs_ica; case: ifP=> // *.
    exact/fs_ica_irrefl/acyc_irrefl/lfsp_acyclic/lfsp_supp_closed.
  rewrite? delete_fs_ca; case: ifP=> [_|_ /andP[/eqP->]] //.
  case: ifP=> [_|_ /andP[? /eqP->]] //.
  exact/fs_ca_antisym/lfsp_acyclic/lfsp_supp_closed.
Qed.

Lemma deleteP :  
  [&& lab_defined delete_pre,
      supp_closed delete_pre &
      acyclic (fin_ica delete_pre)].
Proof. by rewrite delete_lab_defined delete_supp_closed delete_acyclic. Qed.

End DeletePre.

Definition delete :=
  if eqP is ReflectT pf then mklFsPoset (deleteP pf) else lFsPoset.empty E L bot.

Definition lfsp_delE: 
  [forall y : finsupp p, ~~ fs_ica p x (val y)] ->
  (finsupp delete = finsupp p `\ x) *
  (fs_lab delete =1 fun e => if e == x then bot else fs_lab p e) *
  (fs_ica delete =2 fun e1 e2 => if e2 != x then fs_ica p e1 e2 else false) *
  (fs_ca delete =2 fun e1 e2 => if e2 != x then fs_ca p e1 e2 else e1 == e2).
Proof.
  move=>*; rewrite /delete; case: eqP=> //= ?.
  do ? split=>>; 
  by rewrite (delete_finsupp, delete_fs_ca, delete_fs_ica, delete_fs_lab).
Qed.

End DeleteMax.

Arguments of_seq E L bot : clear implicits.

Section InterRel.
Context (E : identType) (L : eqType) (bot : L). 
Implicit Types (p : lfsposet E L bot).

Variable (r : rel E).
Hypothesis (refl  : reflexive r).
Hypothesis (trans : transitive r).

Lemma inter_relP p :  
  let q := lFsPrePoset.inter_rel r p in
  [&& lab_defined q,
      supp_closed q &
      acyclic (fin_ica q)].
Proof.
  move: (lfsp_lab_defined p)=> labD.
  move: (lfsp_supp_closed p)=> supcl.
  move: (lfsp_acyclic p)=> acyc.
  apply/and3P; split.
  - exact/lFsPrePoset.inter_rel_lab_defined. 
  - exact/lFsPrePoset.inter_rel_supp_closed. 
  exact/lFsPrePoset.inter_rel_acyclic. 
Qed.

Definition inter_rel p := mklFsPoset (inter_relP p).

End InterRel.

Arguments inter_rel {E L bot} r. 

Section Inter.
Context (E : identType) (L : eqType) (bot : L). 
Implicit Types (p q : lfsposet E L bot).

Definition inter p q := 
  let supcl := lfsp_supp_closed p in
  inter_rel (fs_ca p) (fs_ca_refl p) (fs_ca_trans supcl) q.

End Inter.

Section Restrict.
Context (E : identType) (L : eqType) (bot : L).
Implicit Types (P : pred E).
Implicit Types (p : lfsposet E L bot).

Lemma restrictP P p :  
  let q := lFsPrePoset.restrict P p in
  [&& lab_defined q,
      supp_closed q &
      acyclic (fin_ica q)].
Proof.
  move: (lfsp_lab_defined p)=> labD.
  move: (lfsp_supp_closed p)=> supcl.
  move: (lfsp_acyclic p)=> acyc.
  apply/and3P; split.
  - exact/lFsPrePoset.restrict_lab_defined. 
  - exact/lFsPrePoset.restrict_supp_closed. 
  exact/lFsPrePoset.restrict_acyclic. 
Qed.

Definition restrict P p := mklFsPoset (restrictP P p).

Lemma restrict_valE P p : 
  val (restrict P p) = lFsPrePoset.restrict P p.
Proof. done. Qed.

End Restrict.

Section Relabel.
Context (E : identType) (L1 : eqType) (L2 : eqType) (bot1 : L1) (bot2 : L2). 
Implicit Types (f : L1 -> L2). 
Implicit Types (p : lfsposet E L1 bot1).

(* Hypothesis (flabD : forall e, let l := fs_lab p e in (l == bot1) = (f l == bot2)). *)
(* Hypothesis (flabD : forall l, (l == bot1) = (f l == bot2)). *)
(* Hypothesis (labD : lab_defined p). *)

Lemma relabelP f p : 
  bot_preserving bot1 bot2 f -> finsupp_preserving bot2 p f -> 
  let q := @lFsPrePoset.relabel E L1 L2 bot1 bot2 f p in
  [&& lab_defined q,
      supp_closed q &
      acyclic (fin_ica q)].
Proof.
  move=> fbot fsupp.
  move: (lfsp_lab_defined p)=> labD.
  move: (lfsp_supp_closed p)=> supcl.
  move: (lfsp_acyclic p)=> acyc.
  apply/and3P; split.
  - exact/lFsPrePoset.relabel_lab_defined. 
  - exact/lFsPrePoset.relabel_supp_closed. 
  exact/lFsPrePoset.relabel_acyclic. 
Qed.

Definition relabel f p :=
  match (bot_preserving bot1 bot2 f) && (finsupp_preserving bot2 p f) =P true with
  | ReflectF _  => lFsPoset.empty E L2 bot2
  | ReflectT pf =>
    let: conj fbot fsupp := andP pf in
    mklFsPoset (relabelP fbot fsupp)
  end.

Variable (f : L1 -> L2) (p : lfsposet E L1 bot1).
Hypothesis (fbot : bot_preserving bot1 bot2 f).
Hypothesis (fsupp : finsupp_preserving bot2 p f).

Lemma relabel_valE : 
  val (relabel f p) = @lFsPrePoset.relabel E L1 L2 bot1 bot2 f p.
Proof. 
  rewrite /relabel; case: eqP=> [pf|] //=.
  - by case: (andP pf). 
  by move=> /negP; rewrite negb_and=> /orP[|] /negP. 
Qed.

End Relabel.

Arguments relabel {E L1 L2 bot1 bot2} f p.

Module Export POrder.
Section POrder.
Context {E : identType} {L : eqType}.
Variable (bot : L) (p : lfsposet E L bot).

Definition lfsposet_porderMixin := 
  @LePOrderMixin E (fs_ca p) (fs_sca p) 
    (fs_sca_def p) 
    (fs_ca_refl p) 
    (fs_ca_antisym (lfsp_supp_closed p) (lfsp_acyclic p))
    (fs_ca_trans (lfsp_supp_closed p)). 

Definition lfsposet_porderType := 
  POrderType tt E lfsposet_porderMixin.

(* TODO: rename/restructure? *)
Lemma lfsp_pideal_mixinP (e e' : lfsposet_porderType) :  
  e \in (lfsp_pideal p e') = (e <= e').
Proof. 
  move: (lfsp_supp_closed p)=> supcl.
  move: (lfsp_acyclic p)=> acyc.
  exact/(lfsp_pidealP _ _ supcl acyc).
Qed.

Definition lfsposet_dwFinPOrderMixin := 
  @DwFinPOrder.DwFinPOrder.Mixin E (Order.POrder.class lfsposet_porderType)
    (lfsp_pideal p)
    lfsp_pideal_mixinP.

Definition lfsposet_dwFinPOrderType := 
  @DwFinPOrder.DwFinPOrder.Pack E 
    (DwFinPOrder.DwFinPOrder.Class lfsposet_dwFinPOrderMixin).

Definition lfsposet_lposetMixin := 
  @lPoset.lPoset.Mixin E L 
    (DwFinPOrder.DwFinPOrder.class lfsposet_dwFinPOrderType) 
    (fs_lab p).

Definition lfsposet_lDwFinPosetType := 
  @lDwFinPoset.lDwFinPoset.Pack L E 
    (lDwFinPoset.lDwFinPoset.Class lfsposet_lposetMixin).

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

Definition lfsposet_finPOrderType :=
  [finPOrderType of lfsposet_fin_porderType].

Definition lfsposet_fin_lposetMixin := 
  @lPoset.lPoset.Mixin _ L (Order.POrder.class lfsposet_fin_porderType) (fin_lab p).

Definition lfsposet_fin_lposetType := 
  let cls := lPoset.lPoset.Class lfsposet_fin_lposetMixin in
  @lPoset.lPoset.Pack L lfsposet_finPOrderType cls.

Definition lfsposet_lfinposetType :=
  let finCls := Order.FinPOrder.class lfsposet_finPOrderType in
  let cls := @lFinPoset.lFinPoset.Class _ L finCls lfsposet_fin_lposetMixin in
  @lFinPoset.lFinPoset.Pack L _ cls.

End FinPOrder.
End FinPOrder.

Module Export Syntax. 
Notation "[ 'Event' 'of' p ]" := (lfsposet_lDwFinPosetType p)
  (at level 0, format "[ 'Event'  'of'  p ]") : form_scope.
Notation "[ 'FinEvent' 'of' p ]" := (lfsposet_lfinposetType p)
  (at level 0, format "[ 'FinEvent'  'of'  p ]") : form_scope.
End Syntax.

Module Export Theory.
Section Theory.
Context {E : identType} {L : eqType} {bot : L}.
Implicit Types (p q : lfsposet E L bot).

Lemma fs_labE p : 
  lab =1 fs_lab p :> ([Event of p] -> L).  
Proof. done. Qed.

Lemma fs_caE p : 
  (<=%O) =2 fs_ca p :> rel [Event of p].  
Proof. done. Qed.

Lemma fs_scaE p : 
  (<%O) =2 fs_sca p :> rel [Event of p].  
Proof. done. Qed.

Lemma fin_labE p : 
  lab =1 fin_lab p :> ([FinEvent of p] -> L).  
Proof. done. Qed.

Lemma fin_caE p : 
  (<=%O) =2 fin_ca p :> rel [FinEvent of p].  
Proof. done. Qed.

Lemma fin_scaE p : 
  (<%O) =2 fin_sca p :> rel [FinEvent of p].  
Proof. done. Qed.

Lemma val_ca_mon p : 
  { homo (val : [FinEvent of p] -> [Event of p]) : e1 e2 / e1 <= e2 }.
Proof. 
  move=> x y; rewrite fin_caE fs_caE /fs_ca /=.
  by rewrite !sub_rel_lift_val=> ->.
Qed.

Lemma fs_labNbot p e : 
  (fs_lab p e != bot) = (e \in finsupp p).
Proof. 
  rewrite mem_finsupp /fs_lab /=.
  move: (lfsp_lab_defined p)=> /lab_definedP labP.
  case: finsuppP=> //=.  
  - by rewrite xpair_eqE negb_and eq_refl.
  move: labP=> /[apply]; rewrite /fs_lab.
  case: (p e)=> l es //=.
  by rewrite xpair_eqE negb_and=> ->.
Qed.

Lemma fs_lab_bot p e : 
  (e \notin finsupp p) -> fs_lab p e = bot.
Proof. by rewrite -fs_labNbot negbK=> /eqP. Qed.  

Lemma fs_rcov_fsupp p e :
  {subset (fs_rcov p e) <= (finsupp p)}.
Proof.
  apply/fsubsetP/fsubsetPn=> [[e']] /=.
  move: (lfsp_supp_closed p)=> /supp_closedP. 
  by move=> /[apply][[->]].
Qed.

Lemma lfsposet_eqP p q : 
  reflect ((fs_lab p =1 fs_lab q) * (fs_ica p =2 fs_ica q)) (p == q).
Proof. 
  apply/(equivP idP); split=> [/eqP->|[]] //.
  rewrite /fs_lab /fs_ica=> eq_lab eq_ica.
  apply/eqP/val_inj=> /=.
  apply/fsfunP=> e /=; apply/eqP.
  rewrite /eq_op=> /=; apply/andP; split.
  - by rewrite (eq_lab e).
  apply/fset_eqP=> e'.
  move: (eq_ica e' e)=> /=.
  by rewrite /fs_rcov.
Qed.

Lemma lfsp_tseq_size p : 
  size (lfsp_tseq p) = fs_size p. 
Proof. by rewrite /lfsp_tseq /fs_size size_map size_tseq cardfE. Qed.

Lemma mem_lfsp_tseq p : 
  lfsp_tseq p =i finsupp p.
Proof. 
  rewrite /lfsp_tseq=> e.
  apply/idP/idP.
  - by move=> /mapP [e'] + ->; case: e'.
  move=> in_supp; apply/mapP.
  exists (Sub e in_supp)=> //.
  by rewrite mem_tseq fintype.mem_enum. 
Qed.

Lemma lfsp_tseq_uniq p : 
  uniq (lfsp_tseq p).
Proof. rewrite /lfsp_tseq (map_inj_uniq val_inj); exact/tseq_uniq. Qed.

Lemma lfsp_idx_lt_szE p e :
  (lfsp_idx p e < fs_size p)%N = (e \in finsupp p).
Proof. by rewrite /lfsp_idx -lfsp_tseq_size index_mem mem_lfsp_tseq. Qed.

Lemma lfsp_idx_le_sz p e :
  lfsp_idx p e <= fs_size p.
Proof. rewrite /lfsp_idx -lfsp_tseq_size; exact/index_size. Qed.

Lemma lfsp_idxK p e0 :
  {in finsupp p, cancel (lfsp_idx p) (lfsp_event p e0)}. 
Proof. 
  rewrite /lfsp_idx /lfsp_event=> e eIn.
  by rewrite nth_index ?mem_lfsp_tseq.
Qed.

Lemma lfsp_eventK p e0 :
  {in (< fs_size p), cancel (lfsp_event p e0) (lfsp_idx p)}. 
Proof. 
  rewrite /lfsp_idx /lfsp_event=> n. 
  rewrite inE ltEnat=> nLe.
  rewrite index_uniq ?lfsp_tseq_size //.
  exact/lfsp_tseq_uniq.
Qed.

Lemma lfsp_idx_inj p : 
  { in finsupp p &, injective (lfsp_idx p)}.
Proof. 
  rewrite /lfsp_idx=> e1 e2 e1In e2In.
  by apply/index_inj; rewrite mem_lfsp_tseq.
Qed.

Lemma lfsp_idx_le p e1 e2 : 
  fs_ca p e1 e2 -> (lfsp_idx p e1 <= lfsp_idx p e2)%N.
Proof. 
  rewrite /lfsp_idx /lfsp_tseq /fs_ca /=.
  move=> /orP[/eqP->|]; first exact/leqnn. 
  rewrite /sub_rel_lift /=. 
  case: insubP=> // e1' e1In <-.
  case: insubP=> // e2' e2In <-.
  rewrite !index_map; try exact/val_inj.
  move: (tseq_correct (rgraph (fin_ica p)))=> [tc tin]. 
  pose g := grel (rgraph (fin_ica p)).
  have gE: g =2 (fin_ica p).
  - by move=> x y /=; rewrite /grel /rgraph fintype.mem_enum. 
  move=> ca12; apply/(@acyclic_connect_before _ g)=> //. 
  - rewrite (eq_acyclic gE); exact/lfsp_acyclic.
  by rewrite (eq_connect gE).
Qed.

Lemma lfsp_labels_size p : 
  size (lfsp_labels p) = fs_size p.
Proof. by rewrite /lfsp_labels size_map lfsp_tseq_size. Qed.

Lemma lfsp_labels_Nbot p : 
  bot \notin lfsp_labels p.
Proof. 
  rewrite /lfsp_labels. 
  apply/mapP=> [[e]].
  rewrite mem_lfsp_tseq -fs_labNbot eq_sym. 
  by move=> /negP + /eqP.
Qed.

(* TODO: fs_lab p e = nth bot (lfsp_labels p) (encode p e) ?? *)
Lemma fs_lab_nthE p e :  
  fs_lab p e = nth bot (lfsp_labels p) (lfsp_idx p e).
Proof. 
  rewrite /lfsp_labels /lfsp_idx.
  case: (e \in finsupp p)/idP=> [eIn | /negP enIn].
  - by rewrite (nth_map \i0) ?nth_index ?index_mem ?mem_lfsp_tseq.
  rewrite nth_default ?fs_lab_bot //.
  rewrite size_map memNindex ?lfsp_tseq_size //. 
  by rewrite mem_lfsp_tseq.
Qed.  

End Theory.
End Theory.

Import lPoset.Syntax.

Module Export Hom.
Section Hom.
Context {E1 E2 : identType} {L : eqType} {bot : L}.
Implicit Types (p : lfsposet E1 L bot) (q : lfsposet E2 L bot).
Implicit Types (f : E1 -> E2).

Definition is_hom f p q := 
  let f : [Event of p] -> [Event of q] := f in
  [/\                    {mono f : e / lab e}  
    & {in (finsupp p) &, {homo f : e1 e2 / e1 <= e2}}
  ].

Variables (p : lfsposet E1 L bot) (q : lfsposet E2 L bot).
Variables (f : E1 -> E2) (ff : {ffun [FinEvent of p] -> [FinEvent of q]}).
Hypothesis (feq : forall e : finsupp p, f (val e) = val (ff e)).

Lemma mono_labW : 
  let f : [Event of p] -> [Event of q] := f in
  {mono f : e / lab e} -> [forall e, lab (ff e) == lab e]. 
Proof. 
  move=> /= flab; apply/mono1P=> x. 
  rewrite ?fin_labE -?fin_lab_mono -?feq; exact/flab.
Qed.

Lemma homo_caP : 
  let f : [Event of p] -> [Event of q] := f in
  reflect {in (finsupp p) &, {homo f : e1 e2 / e1 <= e2}}
          [forall e1, forall e2, (e1 <= e2) ==> (ff e1 <= ff e2)]. 
Proof. 
  apply/(equivP (homo2P _ _ _)); split=> fhom x y; last first.
  - rewrite ?fin_caE -?fin_ca_mono -?feq. 
    move=> le_xy; apply/fhom=> //; exact/valP.
  move=> xin yin le_xy.
  have->: x = val (Sub x xin : finsupp p)=> //. 
  have->: y = val (Sub y yin : finsupp p)=> //. 
  rewrite !feq fs_caE fin_ca_mono; apply/fhom. 
  by rewrite fin_caE -fin_ca_mono. 
Qed.

Lemma mono_caP : 
  let f : [Event of p] -> [Event of q] := f in
  reflect {in (finsupp p) &, {mono f : e1 e2 / e1 <= e2}}
          [forall e1, forall e2, (ff e1 <= ff e2) == (e1 <= e2)]. 
Proof. 
  apply/(equivP (mono2P _ _ _)); split=> fmon x y; last first.
  - rewrite ?fin_caE -?fin_ca_mono -?feq -?fs_caE fmon //; exact/valP. 
  move=> xin yin.
  have->: x = val (Sub x xin : finsupp p)=> //. 
  have->: y = val (Sub y yin : finsupp p)=> //. 
  by rewrite ?feq ?fs_caE ?fin_ca_mono -?fin_caE fmon. 
Qed.

Lemma is_hom_fin : 
  is_hom f p q -> lFinPoset.Hom.axiom ff.
Proof. move=> [??]; apply/andP; split; [exact/mono_labW | exact/homo_caP]. Qed.

Hypothesis (fsup : forall e, e \notin finsupp p -> f e \notin finsupp q).

Lemma mono_labS : 
  let f : [Event of p] -> [Event of q] := f in
  [forall e, lab (ff e) == lab e] -> {mono f : e / lab e}. 
Proof. 
  move=> /= /mono1P flab x. 
  case: (x \in finsupp p)/idP=> [xin|xnin].
  - have->: x = val (Sub x xin : finsupp p)=> //.
    rewrite !feq !fs_labE !fin_lab_mono; exact/flab.
  rewrite !fs_labE !fs_lab_bot //; first exact/negP.
  exact/fsup/negP.
Qed.

(* TODO: move this lemma to appropriate place *)
Lemma mono_lab_finsupp e : 
  let f : [Event of p] -> [Event of q] := f in
  {mono f : e / lab e} -> (e \in finsupp p) = (f e \in finsupp q). 
Proof. by move=> /= labf; rewrite -?fs_labNbot -?fs_labE labf. Qed.

Lemma fin_is_hom : 
  lFinPoset.Hom.axiom ff -> is_hom f p q.
Proof. move=> /andP[??]; split; [exact/mono_labS | exact/homo_caP]. Qed.

Definition hom_lift : E1 -> E2 :=
  sub_lift (fun=> fresh_seq (finsupp q)) (fun e => val (ff e)).

Lemma hom_lift_eq (e : finsupp p) : 
  hom_lift (val e) = val (ff e).
Proof. 
  rewrite /hom_lift sub_liftT //=. 
  by move=> ein; rewrite sub_val. 
Qed.

Lemma hom_lift_Nfinsupp e :
  e \notin finsupp p -> hom_lift e \notin finsupp q.
Proof.
  move=> /negP en; rewrite /hom_lift sub_liftF //.
  exact/fresh_seq_nmem.
Qed.

Hypothesis (homf : is_hom f p q).

Lemma is_hom_finsupp e : 
  e \in finsupp p -> (f e) \in finsupp q.
Proof. by rewrite mono_lab_finsupp; case homf. Qed.

Definition hom_down : {ffun [FinEvent of p] -> [FinEvent of q]} := 
  [ffun e => [` is_hom_finsupp (valP e)] ].

Lemma hom_down_eq (e : finsupp p) : 
  f (val e) = val (hom_down e).
Proof. by rewrite ffunE. Qed.

End Hom.

Arguments is_hom {_ _ _ _} _ _.

Section hPreOrder.
Context {E1 E2 : identType} {L : eqType} {bot : L}.
Implicit Types (p : lfsposet E1 L bot) (q : lfsposet E2 L bot).

Definition hom_le p q := 
  let EP := [FinEvent of p] in
  let EQ := [FinEvent of q] in
  ??|{ffun EQ -> EP | lFinPoset.Hom.axiom}|.

Lemma hom_leP p q :
  reflect (exists f, is_hom f q p) (hom_le p q).
Proof. 
  apply/(equivP (fin_inhP _)); split; last first.
  - move=> [] f ax; exists; exists (hom_down ax).
    apply/(is_hom_fin _ ax); exact/hom_down_eq. 
  move=> [] [] ff ax; exists (hom_lift ff). 
  apply/(fin_is_hom _ _ ax); first exact/hom_lift_eq.
  exact/hom_lift_Nfinsupp.
Qed.

Lemma is_hom_in_finsuppE p q f e : 
  is_hom f p q -> (e \in finsupp p) = (f e \in finsupp q).
Proof. move=> [] fmon ?; by rewrite -?fs_labNbot -?fs_labE fmon. Qed.

End hPreOrder.

Section PreOrder.
Context {E : identType} {L : eqType} {bot : L}.
Implicit Types (p q : lfsposet E L bot).

(* TODO: this relation should also be heterogeneous? *)
Definition hom_lt : rel (lfsposet E L bot) := 
  fun p q => (q != p) && (hom_le p q).

Lemma hom_lt_def p q : hom_lt p q = (q != p) && (hom_le p q).
Proof. done. Qed.

Lemma hom_le_refl : reflexive (@hom_le E E L bot). 
Proof. move=> ?; exact/lFinPoset.Hom.hom_le_refl. Qed.

Lemma hom_le_trans : transitive (@hom_le E E L bot). 
Proof. move=> ??? /[swap]; exact/lFinPoset.Hom.hom_le_trans. Qed.

Lemma is_hom_id_finsuppE p q : 
  is_hom id p q -> finsupp p = finsupp q.
Proof. by move=> hf; apply/fsetP=> e; rewrite (is_hom_in_finsuppE _ hf). Qed.

Lemma is_hom_operational p q : 
  is_hom id p q -> operational q -> operational p.
Proof.
  (do ? case)=> _ cm /(operationalP (lfsp_supp_closed _) (lfsp_acyclic _)) sb.
  apply/forall2P=> -[/= ? {}/cm cm [/= ? {}/cm cm]].
  by apply/implyP=> /cm/sb.
Qed.

End PreOrder.

End Hom.

Module Export iHom.
Section iHom.
Context {E1 E2 : identType} {L : eqType} {bot : L}.
Implicit Types (p : lfsposet E1 L bot) (q : lfsposet E2 L bot).
Implicit Types (f : E1 -> E2).

Definition is_ihom f p q := 
  let f : [Event of p] -> [Event of q] := f in
  [/\                    {mono f : e / lab e}  
    , {in (finsupp p) &, {homo f : e1 e2 / e1 <= e2}}
    & {in (finsupp p) &, injective f}
  ].

Variables (p : lfsposet E1 L bot) (q : lfsposet E2 L bot).
Variables (f : E1 -> E2) (ff : {ffun [FinEvent of p] -> [FinEvent of q]}).
Hypothesis (feq : forall e : finsupp p, f (val e) = val (ff e)).

Lemma injective_onP : 
  reflect {in (finsupp p) &, injective f} (injectiveb ff).
Proof. 
  apply/(equivP (injectiveP _)); split=> injf; last first.
  - move=> x y efxy; apply/val_inj/injf; try exact/valP.
    by rewrite ?feq efxy. 
  move=> /= x y xin yin exy. 
  have->: x = val (Sub x xin : finsupp p)=> //. 
  have->: y = val (Sub y yin : finsupp p)=> //. 
  by congr val; apply/injf/val_inj; rewrite -?feq. 
Qed.

Lemma is_ihom_hom : 
  is_ihom f p q -> is_hom f p q.
Proof. by move=> []. Qed.

Lemma is_ihom_fin : 
  is_ihom f p q -> lFinPoset.iHom.axiom ff.
Proof. 
  move=> [???]; apply/and3P; split; 
    [ exact/Hom.mono_labW 
    | exact/Hom.homo_caP 
    | exact/injective_onP 
    ]. 
Qed.

Hypothesis (fsup : forall e, e \notin finsupp p -> f e \notin finsupp q).

Lemma fin_is_ihom : 
  lFinPoset.iHom.axiom ff -> is_ihom f p q.
Proof. 
  move=> /and3P[???]; split; 
    [ exact/Hom.mono_labS 
    | exact/Hom.homo_caP
    | exact/injective_onP 
    ]. 
Qed.

End iHom.

Arguments is_ihom {_ _ _ _} _ _.

Section hPreOrder.
Context {E1 E2 : identType} {L : eqType} {bot : L}.
Implicit Types (p : lfsposet E1 L bot) (q : lfsposet E2 L bot).

(* TODO: rename bhom_preord? *)
Definition ihom_le p q := 
  let EP := [FinEvent of p] in
  let EQ := [FinEvent of q] in
  ??|{ffun EQ -> EP | lFinPoset.iHom.axiom}|.

Lemma ihom_leP p q :
  reflect (exists f, is_ihom f q p) (ihom_le p q).
Proof. 
  apply/(equivP (fin_inhP _)); split; last first.
  - move=> [] f ax; exists; exists (hom_down (is_ihom_hom ax)).
    apply/(is_ihom_fin _ ax); exact/Hom.hom_down_eq. 
  move=> [] [] ff ax; exists (Hom.hom_lift ff). 
  apply/(fin_is_ihom _ _ ax); first exact/Hom.hom_lift_eq.
  exact/Hom.hom_lift_Nfinsupp.
Qed.

Lemma ihom_le_size p q :
  ihom_le p q -> fs_size q <= fs_size p.
Proof.
  rewrite /ihom_le /fs_size ?cardfE=> /lFinPoset.iHom.ihom_leP[/=] f.
  exact/leq_card/(@ihom_inj _ _ _ f).
Qed.

End hPreOrder.

Section PreOrder.
Context (E : identType) (L : eqType) (bot : L).
Implicit Types (p q : lfsposet E L bot).

(* TODO: this relation should also be heterogeneous? *)
Definition ihom_lt : rel (lfsposet E L bot) := 
  fun p q => (q != p) && (ihom_le p q).

Lemma ihom_lt_def p q : ihom_lt p q = (q != p) && (ihom_le p q).
Proof. done. Qed.

Lemma ihom_le_refl : reflexive (@ihom_le E E L bot). 
Proof. move=> ?; exact/lFinPoset.iHom.ihom_le_refl. Qed.

Lemma ihom_le_trans : transitive (@ihom_le E E L bot). 
Proof. move=> ??? /[swap]; exact/lFinPoset.iHom.ihom_le_trans. Qed.

End PreOrder.

End iHom.


Module Export bHom.
Section bHom.
Context {E1 E2 : identType} {L : eqType} {bot : L}.
Implicit Types (p : lfsposet E1 L bot) (q : lfsposet E2 L bot).
Implicit Types (f : E1 -> E2).

Definition is_bhom f p q := 
  let f : [Event of p] -> [Event of q] := f in
  [/\                    {mono f : e / lab e}  
    , {in (finsupp p) &, {homo f : e1 e2 / e1 <= e2}}
    & {on (finsupp q)  , bijective f}
  ].

Variables (p : lfsposet E1 L bot) (q : lfsposet E2 L bot).
Variables (f : E1 -> E2) (ff : {ffun [FinEvent of p] -> [FinEvent of q]}).
Hypothesis (feq : forall e : finsupp p, f (val e) = val (ff e)).

Lemma bijective_onW : 
  let f : [Event of p] -> [Event of q] := f in
  {mono f : e / lab e} -> {on (finsupp q), bijective f} -> bijectiveb ff.
Proof. 
  move=> /= labf; case=> g K K'; apply/bijectiveP.
  have suppg : forall e, e \in finsupp q -> (g e) \in finsupp p.
  - move=> x /[dup] xin; rewrite -fs_labNbot -fs_labNbot -fs_labE -fs_labE. 
    by rewrite -?labf; apply/contra; rewrite K'. 
  pose gg : [FinEvent of q] -> [FinEvent of p] := 
    fun e => Sub (g (val e)) (suppg (val e) (valP e)). 
  exists gg=> e; rewrite /gg; apply/val_inj=> /=; rewrite -?feq /= ?K ?K' //. 
  rewrite -(Hom.mono_lab_finsupp _ labf); exact/valP.
Qed.

Lemma is_bhom_hom : 
  is_bhom f p q -> is_hom f p q.
Proof. by move=> []. Qed.

Lemma is_bhom_fin : 
  is_bhom f p q -> lFinPoset.bHom.axiom ff.
Proof. 
  move=> [???]; apply/and3P; split; 
    [ exact/Hom.mono_labW 
    | exact/Hom.homo_caP 
    | exact/bijective_onW 
    ]. 
Qed.

Hypothesis (fsup : forall e, e \notin finsupp p -> f e \notin finsupp q).

Lemma bijective_onS : 
  let f : [Event of p] -> [Event of q] := f in
  {mono f : e / lab e} -> bijectiveb ff -> {on (finsupp q), bijective f}. 
Proof. 
  move=> /= labf /bijectiveP[] gg K K'. 
  pose g := Hom.hom_lift (finfun gg).
  have geq: forall e, g (val e) = val (gg e). 
  - move=> /= e; rewrite /g /Hom.hom_lift sub_liftT // => ein.
    congr val; rewrite ffunE; congr gg; exact/sub_val. 
  exists g=> [x | x xin]; last first.
  - have->: x = val (Sub x xin : [FinEvent of q]) by done.
    by rewrite geq feq K'.  
  move=> /[dup] fxin; rewrite -(Hom.mono_lab_finsupp _ labf)=> xin.
  have->: x = val (Sub x xin : [FinEvent of p]) by done.
  by rewrite feq geq K.  
Qed.  

Lemma fin_is_bhom : 
  lFinPoset.bHom.axiom ff -> is_bhom f p q.
Proof. 
  move=> /and3P[???]; split; 
    [ exact/Hom.mono_labS 
    | exact/Hom.homo_caP
    | apply/bijective_onS=> //; exact/Hom.mono_labS 
    ].
Qed.

End bHom.

Arguments is_bhom {_ _ _ _} _ _.

Section hPreOrder.
Context {E1 E2 : identType} {L : eqType} {bot : L}.
Implicit Types (p : lfsposet E1 L bot) (q : lfsposet E2 L bot).

(* TODO: rename bhom_preord? *)
Definition bhom_le p q := 
  let EP := [FinEvent of p] in
  let EQ := [FinEvent of q] in
  ??|{ffun EQ -> EP | lFinPoset.bHom.axiom}|.

Lemma bhom_leP p q :
  reflect (exists (f : E2 -> E1), is_bhom f q p) (bhom_le p q).
Proof. 
  apply/(equivP (fin_inhP _)); split; last first.
  - move=> [] f ax; exists; exists (hom_down (is_bhom_hom ax)).
    apply/(is_bhom_fin _ ax); exact/Hom.hom_down_eq. 
  move=> [] [] ff ax; exists (Hom.hom_lift ff). 
  apply/(fin_is_bhom _ _ ax); first exact/Hom.hom_lift_eq.
  exact/Hom.hom_lift_Nfinsupp.
Qed.

Lemma bhom_ihom_le p q : 
  bhom_le p q -> ihom_le p q.
Proof.
  move=> /lFinPoset.bHom.bhom_leP /= [f]. 
  apply/lFinPoset.iHom.ihom_leP; eexists; exact/f.
Qed.

Lemma bhom_le_size p q :
  bhom_le p q -> fs_size p = fs_size q.
Proof.
  rewrite /bhom_le /fs_size ?cardfE=> /lFinPoset.bHom.bhom_leP [/=] f.
  by move: (bij_eq_card (bhom_bij f)).
Qed.

End hPreOrder.

Section PreOrder.
Context (E : identType) (L : eqType) (bot : L).
Implicit Types (p q : lfsposet E L bot).

(* TODO: this relation should also be heterogeneous? *)
Definition bhom_lt : rel (lfsposet E L bot) := 
  fun p q => (q != p) && (bhom_le p q).

Definition lin E L bot (p : lfsposet E L bot) : pred (seq L) :=
  [pred ls | bhom_le (lFsPoset.of_seq E L bot ls) p].

Lemma bhom_lt_def p q : bhom_lt p q = (q != p) && (bhom_le p q).
Proof. done. Qed.

Lemma bhom_le_refl : reflexive (@bhom_le E E L bot). 
Proof. move=> ?; exact/lFinPoset.bHom.bhom_le_refl. Qed.

Lemma bhom_le_trans : transitive (@bhom_le E E L bot). 
Proof. move=> ??? /[swap]; exact/lFinPoset.bHom.bhom_le_trans. Qed.

Lemma is_bhom_idE p q  : 
  is_bhom id p q <-> is_hom id p q.
Proof. 
  split; first exact/is_bhom_hom.  
  move=> [] *; split=> //; by exists id.
Qed.

End PreOrder.

End bHom.


Module Export Emb.
Section Emb.
Context {E1 E2 : identType} {L : eqType} {bot : L}.
Implicit Types (p : lfsposet E1 L bot) (q : lfsposet E2 L bot).
Implicit Types (f : E1 -> E2).

Definition is_emb f p q := 
  let f : [Event of p] -> [Event of q] := f in
  [/\                    {mono f : e / lab e}  
    & {in (finsupp p) &, {mono f : e1 e2 / e1 <= e2}}
  ].

Variables (p : lfsposet E1 L bot) (q : lfsposet E2 L bot).
Variables (f : E1 -> E2) (ff : {ffun [FinEvent of p] -> [FinEvent of q]}).
Hypothesis (feq : forall e : finsupp p, f (val e) = val (ff e)).

Lemma is_emb_hom : 
  is_emb f p q -> is_hom f p q.
Proof. by move=> [? fmon]; split=> // ????; rewrite fmon. Qed.

Lemma is_emb_fin : 
  is_emb f p q -> lFinPoset.Emb.axiom ff.
Proof. 
  move=> [??]; apply/andP; split; 
    [ exact/Hom.mono_labW 
    | exact/Hom.mono_caP 
    ]. 
Qed.

Hypothesis (fsup : forall e, e \notin finsupp p -> f e \notin finsupp q).

Lemma fin_is_emb : 
  lFinPoset.Emb.axiom ff -> is_emb f p q.
Proof. 
  move=> /andP[???]; split; 
    [ exact/Hom.mono_labS 
    | exact/Hom.mono_caP
    ].
Qed.

End Emb.

Arguments is_emb {_ _ _ _} _ _.

Section hPreOrder.
Context {E1 E2 : identType} {L : eqType} {bot : L}.
Implicit Types (p : lfsposet E1 L bot) (q : lfsposet E2 L bot).

Definition emb_le p q := 
  let EP := [FinEvent of p] in
  let EQ := [FinEvent of q] in
  ??|{ffun EQ -> EP | lFinPoset.Emb.axiom}|.

Lemma emb_leP p q :
  reflect (exists (f : E2 -> E1), is_emb f q p) (emb_le p q).
Proof. 
  apply/(equivP (fin_inhP _)); split; last first.
  - move=> [] f ax; exists; exists (hom_down (is_emb_hom ax)).
    apply/(is_emb_fin _ ax); exact/Hom.hom_down_eq. 
  move=> [] [] ff ax; exists (Hom.hom_lift ff). 
  apply/(fin_is_emb _ _ ax); first exact/Hom.hom_lift_eq.
  exact/Hom.hom_lift_Nfinsupp.
Qed.

Lemma emb_ihom_le p q : 
  emb_le p q -> ihom_le p q.
Proof.
  move=> /lFinPoset.Emb.emb_leP /= [f]. 
  apply/lFinPoset.iHom.ihom_leP; eexists; exact/f.
Qed.

Lemma emb_le_size p q :
  emb_le p q -> fs_size q <= fs_size p.
Proof. by move=> /emb_ihom_le /ihom_le_size. Qed.

Lemma emb_fs_ca f p q (X : {fset E1}) : is_emb f p q -> {in X &, injective f} ->
  let f : [Event of p] -> [Event of q] := f in
  {in X &, {mono f : e1 e2 / e1 <= e2}}.
Proof.
  move=> [] labf monf injf /= e1 e2 in1 in2 /=; apply/esym.
  case: ((e1 \notin finsupp p) || (e2 \notin finsupp p))/idP=> [ns|].
  - apply/idP/idP=> /(fs_ca_nsupp (lfsp_supp_closed _) (lfsp_acyclic _)). 
    + move=> /(_ ns) /=-> //; exact/fs_ca_refl.
    rewrite -?(Hom.mono_lab_finsupp _ labf) ns. 
    move=> /(_ erefl)/(injf _ _ in1 in2)->.
    exact/fs_ca_refl.
  move/negP; rewrite negb_or ?negbK=> /andP[*].
  by rewrite -?fs_caE monf.
Qed.

Lemma emb_dw_clos f p q es e :  
  is_emb f p q -> es `<=` finsupp p -> f @` es `<=` finsupp q ->
  e \in lfsp_dw_clos p es = (f e \in lfsp_dw_clos q (f @` es)).
Proof.
  case=> labf monf subs subsf.
  have psupcl : supp_closed p by apply/lfsp_supp_closed.
  have qsupcl : supp_closed q by apply/lfsp_supp_closed.
  have pacyc : acyclic (fin_ica p) by apply/lfsp_acyclic.
  have qacyc : acyclic (fin_ica q) by apply/lfsp_acyclic.
  apply/lfsp_dw_closP/lfsp_dw_closP=> // [[e']|[e']]/[swap].
  - move=>/[dup] ? /(fsubsetP subs) ? ca. 
    exists (f e'); rewrite -?fs_caE ?monf //.
    + move: ca=> /(supp_closed_ca psupcl pacyc) /orP[/eqP->|/andP[]] //.
    by apply/imfsetP; exists e'.
  case/imfsetP=> /= {}e' /[swap]->. 
  move=> /[dup] ? /(fsubsetP subs) ein ca; exists e'=> //.
  rewrite -fs_caE -monf //. 
  move: ca=> /(supp_closed_ca qsupcl qacyc). 
  rewrite -?(Hom.mono_lab_finsupp _ labf). 
  move=> /orP[/eqP|/andP[]] //.
  rewrite (Hom.mono_lab_finsupp _ labf)=> ->.   
  by rewrite -(Hom.mono_lab_finsupp _ labf). 
Qed.

End hPreOrder.

Section PreOrder.
Context (E : identType) (L : eqType) (bot : L).
Implicit Types (p q : lfsposet E L bot).

(* TODO: this relation should also be heterogeneous? *)
Definition emb_lt : rel (lfsposet E L bot) := 
  fun p q => (q != p) && (emb_le p q).

Lemma emb_lt_def p q : emb_lt p q = (q != p) && (emb_le p q).
Proof. done. Qed.

Lemma emb_le_refl : reflexive (@emb_le E E L bot). 
Proof. move=> ?; exact/lFinPoset.Emb.emb_le_refl. Qed.

Lemma emb_le_trans : transitive (@emb_le E E L bot). 
Proof. move=> ??? /[swap]; exact/lFinPoset.Emb.emb_le_trans. Qed.

End PreOrder.

End Emb.


Module Export Iso.
Section Iso.
Context {E1 E2 : identType} {L : eqType} {bot : L}.
Implicit Types (p : lfsposet E1 L bot) (q : lfsposet E2 L bot).
Implicit Types (f : E1 -> E2).

Definition is_iso f p q := 
  let f : [Event of p] -> [Event of q] := f in
  [/\                    {mono f : e / lab e}  
    , {in (finsupp p) &, {mono f : e1 e2 / e1 <= e2}}
    & {on (finsupp q)  , bijective f}
  ].

Variables (p : lfsposet E1 L bot) (q : lfsposet E2 L bot).
Variables (f : E1 -> E2) (ff : {ffun [FinEvent of p] -> [FinEvent of q]}).
Hypothesis (feq : forall e : finsupp p, f (val e) = val (ff e)).

Lemma is_iso_hom : 
  is_iso f p q -> is_hom f p q.
Proof. by move=> [? fmon ?]; split=> // ????; rewrite fmon. Qed.

Lemma is_iso_bhom : 
  is_iso f p q -> is_bhom f p q.
Proof. by move=> [? fmon ?]; split=> // ????; rewrite fmon. Qed.

Lemma is_iso_emb : 
  is_iso f p q -> is_emb f p q.
Proof. by move=> []. Qed.

Lemma is_iso_fin : 
  is_iso f p q -> lFinPoset.Iso.axiom ff.
Proof. 
  move=> [???]; apply/and3P; split; 
    [ exact/Hom.mono_labW 
    | exact/Hom.mono_caP 
    | exact/bHom.bijective_onW 
    ]. 
Qed.

Hypothesis (fsup : forall e, e \notin finsupp p -> f e \notin finsupp q).

Lemma fin_is_iso : 
  lFinPoset.Iso.axiom ff -> is_iso f p q.
Proof. 
  move=> /and3P[???]; split; 
    [ exact/Hom.mono_labS 
    | exact/Hom.mono_caP
    | apply/bHom.bijective_onS=> //; exact/Hom.mono_labS 
    ].
Qed.

End Iso.

Section hEquiv.
Context {E1 E2 : identType} {L : eqType} {bot : L}.
Implicit Types (p : lfsposet E1 L bot) (q : lfsposet E2 L bot).

Definition iso_eqv p q := 
  let EP := [FinEvent of p] in
  let EQ := [FinEvent of q] in
  ??|{ffun EQ -> EP | lFinPoset.Iso.axiom}|.

Lemma iso_eqvP p q :
  reflect 
    (exists (f : E2 -> E1), is_iso f q p) (iso_eqv p q).
Proof. 
  apply/(equivP (fin_inhP _)); split; last first.
  - move=> [] f ax; exists; exists (hom_down (is_iso_hom ax)).
    apply/(is_iso_fin _ ax); exact/Hom.hom_down_eq. 
  move=> [] [] ff ax; exists (Hom.hom_lift ff). 
  apply/(fin_is_iso _ _ ax); first exact/Hom.hom_lift_eq.
  exact/Hom.hom_lift_Nfinsupp.
Qed.

Lemma iso_bhom_le p q : 
  iso_eqv p q -> bhom_le p q.
Proof.
  move=> /lFinPoset.Iso.iso_eqvP /= [f]. 
  apply/lFinPoset.bHom.bhom_leP; eexists; exact/f.
Qed.

Lemma iso_emb_le p q : 
  iso_eqv p q -> emb_le p q.
Proof.
  move=> /lFinPoset.Iso.iso_eqvP /= [f]. 
  apply/lFinPoset.Emb.emb_leP; eexists; exact/f.
Qed.

Lemma iso_ihom_le p q : 
  iso_eqv p q -> ihom_le p q.
Proof. by move=> /iso_bhom_le /bhom_ihom_le. Qed.

Lemma iso_eqv_size p q :
  iso_eqv p q -> fs_size p = fs_size q.
Proof. by move=> /iso_bhom_le /bhom_le_size. Qed.

Lemma bhom_factor p q : bhom_le p q -> 
  exists2 q' : lfsposet E1 L bot, iso_eqv q' q & is_hom id q' p.
Proof.
  case/bhom_leP=> f [labf homf [/= g K K']]. 
  set fE := finsupp p.
  set fl : fE -> L := fun e => lab (g (val e) : [Event of q]).
  set ca  : rel E1  := fun e1 e2 => 
    (e1 == e2) || 
    [&& fs_ca q (g e1) (g e2), e1 \in finsupp p & e2 \in finsupp p].
  have [: a1 a2 a3 a4] @q' := 
    @lFsPoset.build_cov E1 L bot fE fl ca a1 a2 a3 a4.
  - by case=> e ein; rewrite /= /fl -labf K' // fs_labE fs_labNbot. 
  - by move=> ?; rewrite /ca eqxx.
  - move=> e1 e2 /andP[] /orP[/eqP-> //|/and3P[+ e1In e2In]].
    move=> /homf; rewrite !(Hom.mono_lab_finsupp _ labf) ?K' //. 
    move=>/(_ e1In e2In)/[swap].
    case/orP=>[/eqP->//|/and3P[+??]].
    move=> /homf; rewrite !(Hom.mono_lab_finsupp _ labf) ?K' //. 
    move=>/(_ e2In e1In)/[swap].
    move=> ??; suff: e1 = e2 :> [Event of p] by done.
    exact/le_anti/andP.
  - set ft := (fs_ca_trans (lfsp_supp_closed q)).
    move=>>; rewrite /ca => /orP[/eqP->//|/and3P[/[dup] fc /ft tr i1 i2]].
    move/orP=>[/eqP<-|]; rewrite ?fc ?i1 i2 //=.
    by move/andP=> [/tr->]->.
  exists q'; first (apply/iso_eqvP=> /=; exists f); repeat split. 
  - move=> x; rewrite ?fs_labE ?/(_ <= _) /=.
    rewrite lFsPrePoset.build_lab /sub_lift.
    case: insubP=> /=; rewrite /fl.
    + by case=> /= ???->; rewrite K.
    by rewrite -fs_labNbot -?fs_labE labf eq_sym negbK=> /eqP. 
  - move=> e1 e2 e1In e2In; rewrite ?/(_ <= _) /=.
    rewrite lFsPrePoset.build_cov_ca_wf ?/ca //; last first.
    + move=> x y /orP[/eqP->|/and3P[]] //=; rewrite ?/dhrel_one ?eqxx //.
      by rewrite /fE=> ? -> ->.
    rewrite ?K -?(Hom.mono_lab_finsupp _ labf) //.
    rewrite e1In e2In !andbT; apply: orb_idl=> /eqP.
    suff: {on finsupp p &, injective f}.
    - move=> /[apply]; rewrite -?(Hom.mono_lab_finsupp _ labf) //.
      move=> /(_ e1In e2In) ->; exact/fs_ca_refl. 
    apply/on_can_inj; exact/K.
  - by exists g; rewrite lFsPrePoset.build_finsupp.
  - move=> e; rewrite ?fs_labE lFsPrePoset.build_lab /sub_lift.
    case: insubP=> /= [[/=>?]|].
    + rewrite /fl -labf fs_labE /= K' // =>-> //.
    by rewrite -fs_labNbot negbK=>/eqP->.
  move=>>; rewrite ?/(_ <= _) /= lFsPrePoset.build_cov_ca // /ca /fE.
  rewrite lFsPrePoset.build_finsupp // => ??.
  case/orP=> [/eqP->|]; first exact/fs_ca_refl.
  case/and3P=> /orP[/eqP->*|]; first exact/fs_ca_refl.
  by case/and3P=> /homf; rewrite !(Hom.mono_lab_finsupp _ labf) ?K' //. 
Qed.

Definition upd_iso (f : E1 -> E2) p q e' x y e := 
 if e \in finsupp p then f e else if e == x then y else e'.

Section Update.
Variables (f : E1 -> E2) (p : lfsposet E1 L bot) (q : lfsposet E2 L bot).
Variables (e' : E2) (x : E1) (y : E2).

Hypothesis (en' : e' \notin finsupp q).
Hypothesis (xn  : x  \notin finsupp p).
Hypothesis (yn  : y  \notin finsupp q).
Hypothesis (neq : e' != y).

Local Notation upd_iso f := (upd_iso f p q e' x y).

Lemma upd_iso_supp e : 
  e \in finsupp p -> upd_iso f e = f e.  
Proof. by rewrite /(upd_iso f); move=> ->. Qed.

Lemma upd_iso_delta : 
  upd_iso f x = y.  
Proof. by rewrite /(upd_iso f) eqxx; move: (negP xn); case: ifP=> //. Qed.

Lemma upd_iso_delta_eq e : 
  let f : [Event of p] -> [Event of q] := f in
  {mono f : e / lab e} -> (upd_iso f e == y) = (e == x).
Proof. 
  move=> /= labf.
  apply/idP/idP=> [|/eqP->]; rewrite ?upd_iso_delta //.
  rewrite /(upd_iso f); repeat case: ifP=> //.
  - move=> /[swap]; move: yn=> /[swap] /eqP <-.  
    by rewrite -(Hom.mono_lab_finsupp _ labf)=> /negP.
  by move: (negP neq).
Qed.

(* TODO: this should be simplified 
 * (perhaps, using normalized posets?) 
 *)
Lemma update_iso : 
  is_iso f p q -> is_iso (upd_iso f) p q.
Proof.
  move=> [] labf monof [/= g] K K'; split; rewrite /(upd_iso f).
  - move=> e /=; case: ifP=> [? | /negP en]; first exact/labf. 
    rewrite !fs_labE !fs_lab_bot //; first exact/negP. 
    by case: ifP.
  - move=> e1 e2 /= /[dup] ? -> /[dup] ? ->; exact/monof.
  exists g=> z /=. 
  - case: ifP=>[?? |]; first exact/K. 
    move: en'=> /negP ?; move: yn=> /negP ?.
    by case: ifP. 
  case: ifP=> [?? |]; first exact/K'.
  move=> /[swap] /[dup] ?.
  rewrite -{1}[z]K' //. 
  by rewrite -(Hom.mono_lab_finsupp _ labf) => ->. 
Qed.

End Update.

End hEquiv.

Section Equiv.
Context (E : identType) (L : eqType) (bot : L).
Implicit Types (p q : lfsposet E L bot).

(* TODO: generalize the proofs to arbitary `T -> T -> Type`? *)
Lemma iso_eqv_refl : reflexive (@iso_eqv E E L bot).
Proof. 
  move=> p; apply/lFinPoset.Iso.iso_eqvP. 
  exists; exact/[iso of idfun]. 
Qed.

Lemma iso_eqv_sym : symmetric (@iso_eqv E E L bot).
Proof. 
  move=> p q.
  apply/idP/idP=> /lFinPoset.Iso.iso_eqvP [f]; 
    apply/lFinPoset.Iso.iso_eqvP; 
    exists; exact/[iso of bhom_inv f].
Qed.

Lemma iso_eqv_trans : transitive (@iso_eqv E E L bot).
Proof. 
  rewrite /iso_eqv=> p q r.
  move=> /lFinPoset.Iso.iso_eqvP [f] /lFinPoset.Iso.iso_eqvP [g]. 
  apply/lFinPoset.Iso.iso_eqvP. 
  exists; exact/[iso of f \o g].
Qed.

Lemma iso_ihom_le_antisym p q : 
  ihom_le p q -> ihom_le q p -> iso_eqv p q.
Proof.
  move=> /lFinPoset.iHom.ihom_leP[f] /lFinPoset.iHom.ihom_leP[g].
  apply/lFinPoset.Iso.iso_eqvP; exists; exists f; split.
  - exact/(lab_preserving f).
  - apply/inj_le_homo_mono; try exact/ihom_inj; try exact/ca_monotone.
  apply/inj_inj_bij; exact/ihom_inj. 
Qed.

Lemma iso_bhom_le_antisym p q : 
  bhom_le p q -> bhom_le q p -> iso_eqv p q.
Proof. move=> /bhom_ihom_le + /bhom_ihom_le; exact/iso_ihom_le_antisym. Qed.

Lemma iso_emb_le_antisym p q : 
  emb_le p q -> emb_le q p -> iso_eqv p q.
Proof. move=> /emb_ihom_le + /emb_ihom_le; exact/iso_ihom_le_antisym. Qed.

End Equiv.

End Iso.

End lFsPoset.

Export lFsPoset.Def.
Export lFsPoset.Instances.
Export lFsPoset.Syntax.
Export lFsPoset.Theory.

Export lFsPoset.Hom.
Export lFsPoset.iHom.
Export lFsPoset.bHom.
Export lFsPoset.Emb.
Export lFsPoset.Iso.

Module Pomset.

Import lPoset.Syntax.
Import lFsPoset.Syntax.

Module Export Def.
Section Def.  
Context {E : identType} {L : choiceType} {bot : L}.

Canonical iso_equiv_rel := 
  EquivRel iso_eqv 
    (@iso_eqv_refl E L bot) 
    (@iso_eqv_sym E L bot) 
    (@iso_eqv_trans E L bot).

Definition pomset := {eq_quot iso_eqv}.

Canonical pomset_quotType := [quotType of pomset].
Canonical pomset_eqType := [eqType of pomset].
Canonical pomset_choiceType := [choiceType of pomset].
Canonical pomset_eqQuotType := [eqQuotType iso_eqv of pomset].

Definition pom : lfsposet E L bot -> pomset := \pi.

Implicit Types (p : pomset).

Coercion lfsposet_of p : lfsposet E L bot := repr p.

(* TODO: specialize lemma event further? use is_iso equivalence directly? *)
Lemma pomP q : 
  pi_spec pomset_quotType q (repr (pom q)).
Proof. by case: piP. Qed. 

End Def.
End Def.

Arguments pomset E L bot : clear implicits.

Section OfSeq.
Context (E : identType) (L : choiceType) (bot : L). 
Implicit Types (p : pomset E L bot).
Implicit Types (ls : seq L).

Definition of_seq ls : pomset E L bot := 
  pom (@lFsPoset.of_seq E L bot ls).

End OfSeq.

Section InterRel.
Context (E : identType) (L : choiceType) (bot : L). 
Implicit Types (p : pomset E L bot).

Variable (r : rel E).
Hypothesis (refl  : reflexive r).
Hypothesis (trans : transitive r).

Definition inter_rel p : pomset E L bot := 
  \pi (lFsPoset.inter_rel r refl trans p).

End InterRel.

Arguments inter_rel {E L bot} r. 

Section Inter.
Context (E : identType) (L : choiceType) (bot : L). 
Implicit Types (p q : pomset E L bot).

Definition inter p q : pomset E L bot := 
  \pi (lFsPoset.inter p q).

End Inter.

Section Restrict.
Context (E : identType) (L : choiceType) (bot : L). 
Implicit Types (P : pred E).
Implicit Types (p q : pomset E L bot).

Definition restrict P p : pomset E L bot := 
  \pi (lFsPoset.restrict P p).

End Restrict.


Section Relabel.
Context (E : identType) (L1 L2 : choiceType) (bot1 : L1) (bot2 : L2). 
Implicit Types (f : L1 -> L2).
Implicit Types (p : pomset E L1 bot1).

Definition relabel f p : pomset E L2 bot2 := 
  \pi (@lFsPoset.relabel E L1 L2 bot1 bot2 f p).

End Relabel.

Arguments relabel {E L1 L2 bot1 bot2} f p.

Import lPoset.Syntax.
Import lFsPoset.Syntax.

Module Export iHom.
Module Export POrder.
Section POrder.
Implicit Types (E : identType) (L : choiceType).

Lemma pom_ihom_le E1 E2 L bot (p : lfsposet E1 L bot) (q : lfsposet E2 L bot) :
  ihom_le (repr (pom p)) (repr (pom q)) = ihom_le p q.
Proof.
  rewrite /ihom_le. 
  case: pomP=> q' /eqmodP/lFinPoset.Iso.iso_eqvP[f]. 
  case: pomP=> p' /eqmodP/lFinPoset.Iso.iso_eqvP[g].
  apply/lFinPoset.iHom.ihom_leP/lFinPoset.iHom.ihom_leP=> [][h]; exists. 
  - exact/[ihom of g \o h \o [iso of (bhom_inv f)]].
  exact/[ihom of [iso of (bhom_inv g)] \o h \o f].
Qed.

Context {E : identType} {L : choiceType} {bot : L}.
Implicit Types (p q : pomset E L bot). 

Lemma pom_ihom_mono :
  {mono (@pom E L bot) : p q / ihom_le p q >-> ihom_le (repr p) (repr q)}.
Proof. exact/pom_ihom_le. Qed.

Canonical ihom_le_quot_mono2 := PiMono2 pom_ihom_mono.

(* TODO: porder instance for ihom_le *)

End POrder.
End POrder.
End iHom.

Module Export bHom.
Module Export POrder.
Section POrder.
Implicit Types (E : identType) (L : choiceType).

Lemma pom_bhom_le E1 E2 L bot (p : lfsposet E1 L bot) (q : lfsposet E2 L bot) :
  bhom_le (repr (pom p)) (repr (pom q)) = bhom_le p q.
Proof.
  rewrite /bhom_le. 
  case: pomP=> q' /eqmodP/lFinPoset.Iso.iso_eqvP[f]. 
  case: pomP=> p' /eqmodP/lFinPoset.Iso.iso_eqvP[g].
  apply/lFinPoset.bHom.bhom_leP/lFinPoset.bHom.bhom_leP=> [][h]; exists.
  - exact/[bhom of g \o h \o [iso of bhom_inv f]].
  exact/[bhom of [iso of bhom_inv g] \o h \o f].
Qed.

Lemma pom_bhom_le1 E1 E2 L bot (p : lfsposet E1 L bot) (q : lfsposet E2 L bot) :
  bhom_le p (repr (pom q)) = bhom_le p q.
Proof.
  rewrite /bhom_le. 
  case: pomP=> q' /eqmodP/lFinPoset.Iso.iso_eqvP[f]. 
  (* case: pomP=> p' /eqmodP/lFinPoset.fisoP[g]. *)
  apply/lFinPoset.bHom.bhom_leP/lFinPoset.bHom.bhom_leP=> [][h]; exists.
  - exact/[bhom of h \o [iso of (bhom_inv f)]].
  exact/[bhom of h \o f].
Qed.

Context {E : identType} {L : choiceType} {bot : L}.
Implicit Types (p q : pomset E L bot). 

Lemma pom_bhom_mono :
  {mono (@pom E L bot) : p q / bhom_le p q >-> bhom_le (repr p) (repr q)}.
Proof. exact/pom_bhom_le. Qed.

Lemma pom_lin_mono l :
  {mono (@pom E L bot) : p / l \in lin p >-> l \in lin (repr p)}.
Proof. exact/pom_bhom_le1. Qed.

Canonical bhom_le_quote_mono2 := PiMono2 pom_bhom_mono.
Canonical lin_quote_mono2 l := PiMono1 (pom_lin_mono l).

Lemma pom_bhom_le_refl : 
  reflexive (@bhom_le E E L bot : rel (pomset E L bot)). 
Proof. exact/bhom_le_refl. Qed.

Lemma pom_bhom_le_antisym : 
  antisymmetric (@bhom_le E E L bot : rel (pomset E L bot)). 
Proof. 
  move=> p q; rewrite -[p]reprK -[q]reprK !piE.
  move=> /andP[??]; exact/eqmodP/iso_bhom_le_antisym.
Qed.

Lemma pom_bhom_le_trans : 
  transitive (@bhom_le E E L bot : rel (pomset E L bot)). 
Proof. exact/bhom_le_trans. Qed.

Lemma disp : unit. 
Proof. exact: tt. Qed.

Definition pomset_bhomPOrderMixin := 
  @LePOrderMixin _ 
    (@bhom_le E E L bot : rel (pomset E L bot)) 
    (fun p q => (q != p) && (bhom_le p q))
    (fun p q => erefl) pom_bhom_le_refl pom_bhom_le_antisym pom_bhom_le_trans. 

Canonical pomset_bhomPOrderType := 
  POrderType disp (pomset E L bot) pomset_bhomPOrderMixin.

Lemma pom_bhom_leE p q : p <= q = bhom_le p q.
Proof. done. Qed.

End POrder.
End POrder.
End bHom.

Module Export Theory.
Section Theory.
Context {E : identType} {L : choiceType} (bot : L).
Implicit Types (p q : pomset E L bot).

Lemma iso_eqv_pom (p : lfsposet E L bot) :
  iso_eqv p (pom p).
Proof. by rewrite -eqmodE piK. Qed.

Lemma bhom_lin p q :
  p <= q -> {subset (lin p) <= (lin q)}.
Proof.
  move=> pLq ?; rewrite /lin ?/(_ \in _) //=.
  by move=> /bhom_le_trans /(_ pLq).
Qed.

End Theory.
End Theory.

End Pomset.

Export Pomset.Def.
Export Pomset.iHom.POrder.
Export Pomset.bHom.POrder.
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
Context (E : identType) (L : choiceType) (bot : L).

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


Section OfSeq.
Context (E : identType) (L : choiceType) (bot : L). 
Implicit Types (p : lfspreposet E L bot).
Implicit Types (ls : seq L).

Lemma of_seq_total ls : 
  let p := @Pomset.of_seq E L bot ls in
  total (fin_ca p).   
Proof. 
  pose p := @lFsPoset.of_seq E L bot ls.
  rewrite /Pomset.of_seq=> /= e1 e2.
  move: (iso_eqv_pom p)=> /lFinPoset.Iso.iso_eqvP [f]. 
  move: (lFsPoset.of_seq_total (f e1) (f e2)).
  repeat rewrite -fin_caE.
  by rewrite !(ca_reflecting f).
Qed.

Definition of_seq ls := 
  mkTomset (introT (totalP _) (@of_seq_total ls)).

End OfSeq.

Module Export Theory.
Section Theory.
Context {E : identType} {L : choiceType} (bot : L).
Implicit Types (t u : tomset E L bot).

Lemma tomset_labelsK : 
  cancel (@lfsp_labels E L bot : tomset E L bot -> seq L) (@of_seq E L bot).
Proof. 
  move=> t; apply/val_inj/esym/eqP=> /=.
  rewrite eqquot_piE iso_eqv_sym.
  apply/iso_eqvP.
  pose u := lFsPoset.of_seq E L bot (lfsp_labels t).
  pose f : [Event of t] -> [Event of u] := 
    fun e => decode (lfsp_idx t e).
  move: (lfsp_labels_Nbot t)=> labD.
  have usz : fs_size u = fs_size t.
  - by rewrite lFsPoset.of_seq_size labD lfsp_labels_size. 
  have uconseq: (conseq_num u).
  - exact/lFsPoset.of_seq_conseq_num.
  exists f; split; try constructor=> //=.
  - move=> e; rewrite !fs_labE /=. 
    rewrite lFsPoset.of_seq_labE labD.
    by rewrite decodeK fs_lab_nthE.
  - move=> e1 e2 e1In e2In; rewrite !fs_caE /=.
    rewrite lFsPoset.of_seq_caE labD andbT. 
    rewrite !conseq_num_mem // !decodeK !usz !lfsp_idx_lt_szE.
    rewrite ident_leE /f !decodeK. 
    apply/idP/idP=> [/orP[|] |]; last 1 first.
    + by rewrite e1In e2In leEnat=> /lfsp_idx_le ->. 
    + move=> /eqP /decode_inj /lfsp_idx_inj -> //; exact/fs_ca_refl.
    move=> /and3P[le12 ??].  
    move: (tomset_total_in e1In e2In).  
    rewrite !fs_caE=> /orP[|] // => /lfsp_idx_le le21.
    suff->: e1 = e2 by exact/fs_ca_refl.
    exact/(lfsp_idx_inj e1In e2In)/le_anti/andP. 
  pose g : [Event of u] -> [Event of t] := 
    fun e => lfsp_event t \i0 (encode e).
  exists g=> e; rewrite !conseq_num_mem // /f /g !usz ?decodeK.
  - rewrite lfsp_idx_lt_szE; exact/lfsp_idxK. 
  by move=> ?; rewrite lfsp_eventK ?encodeK //. 
Qed.

End Theory.
End Theory.

End Tomset.

Export Tomset.Def.
Export Tomset.Theory.

