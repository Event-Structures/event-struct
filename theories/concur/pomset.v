From Coq Require Import Relations.
From RelationAlgebra Require Import lattice monoid rel boolean kat_tac.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat seq tuple.
From mathcomp Require Import eqtype choice order generic_quotient.
From mathcomp Require Import fintype finfun finset fingraph finmap zify.
From mathcomp.tarjan Require Import extra acyclic kosaraju acyclic_tsorted. 
From eventstruct Require Import utils rel relalg inhtype order ident lposet.

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

(* TODO: rename lfsp_size? *)
Definition fs_size p : nat := #|` finsupp p|.

Definition lab_defined p := 
  [forall e : finsupp p, fs_lab p (val e) != bot].

Definition supp_closed p := 
  [forall e : finsupp p, fs_rcov p (val e) `<=` finsupp p].

(* TODO: better name? *)
Definition operational p := 
  [forall e1 : finsupp p, forall e2 : finsupp p, 
    (fs_ca p (val e1) (val e2)) ==> (val e1 <=^i val e2)
  ].

Definition conseq_num p :=
  finsupp p == [fset e | e in nfresh \i0 (fs_size p)].

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
  move: lsD=> /negP nbl [/= e].
  rewrite ?inE /= in_nfresh encode0 addn0 /= => He.
  apply/negP; move: nbl=> /[swap]/eqP<-.  
  apply; exact/mem_nth.
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
  rewrite !in_fset /mem_fin /=.
  rewrite in_nfresh encode0 addn0 /=.
  rewrite ltnNge negbK=> ?. 
  by rewrite nth_default.
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
  - case=> /= e; rewrite ?inE /= in_nfresh encode0 addn0 /=.
    move=> ?; apply/eqP; move: lsD=> /[swap]<-.
    rewrite mem_nth=> //; lia.
  apply/covP/eqP=> /=; case: e1 e2=> /= e1 i1 [/= e2 i2].
  - case=> _ /andP[ne le nex]; apply/encode_inj; rewrite encode_fresh.
    case: ((encode e1).+1 =P encode e2)=> // ?; case: nex.
    move: i1 i2 le ne; rewrite of_seq_finsupp ?inE ?in_nfresh encode0 addn0 /=.
    rewrite /(_ <=^i _) /= /Ident.Def.ident_le -(inj_eq encode_inj)=>*.
    have IN: (fresh e1 \in [fset e | e in nfresh \i0 (size ls)]).
    - rewrite ?inE in_nfresh encode0 encode_fresh; lia.
    exists [`IN] => /=. 
    rewrite ?/(_ <=^i _) /= ?/Ident.Def.ident_le -(inj_eq encode_inj).
    rewrite -[_ == fresh _](inj_eq encode_inj) ?encode_fresh; lia.
  move=> fE.
  have: e1 <^i e2 by rewrite -fE fresh_lt.
  move=> /[dup]; rewrite {1}lt_neqAle=> /andP[*]; split.
  - move/(congr1 val)=> /=; exact/eqP.
  - rewrite eq_sym; exact/andP.
  case=> -[/= e _]; rewrite -fE ?/(_ <=^i _) /= ?/Ident.Def.ident_le.
  rewrite -(inj_eq encode_inj) -[fresh _ == _](inj_eq encode_inj) encode_fresh.
  lia.
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
Hypothesis (fbot : f bot1 = bot2).
Hypothesis (flabD : [forall e : finsupp p, f (fs_lab p (val e)) != bot2]).

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
  exact/(forallP flabD). 
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
  exact/(forallP flabD). 
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

End Restrict.

Section Relabel.
Context (E : identType) (L1 : eqType) (L2 : eqType) (bot1 : L1) (bot2 : L2). 

Variables (f : L1 -> L2) (p : lfsposet E L1 bot1).
Hypothesis (fbot : f bot1 = bot2).
Hypothesis (flabD : [forall e : finsupp p, f (fs_lab p (val e)) != bot2]).

(* Hypothesis (flabD : forall e, let l := fs_lab p e in (l == bot1) = (f l == bot2)). *)
(* Hypothesis (flabD : forall l, (l == bot1) = (f l == bot2)). *)
(* Hypothesis (labD : lab_defined p). *)

Lemma relabelP :  
  let q := @lFsPrePoset.relabel E L1 L2 bot1 bot2 f p in
  [&& lab_defined q,
      supp_closed q &
      acyclic (fin_ica q)].
Proof.
  move: (lfsp_lab_defined p)=> labD.
  move: (lfsp_supp_closed p)=> supcl.
  move: (lfsp_acyclic p)=> acyc.
  apply/and3P; split.
  - exact/lFsPrePoset.relabel_lab_defined. 
  - exact/lFsPrePoset.relabel_supp_closed. 
  exact/lFsPrePoset.relabel_acyclic. 
Qed.

Definition relabel := mklFsPoset relabelP.

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

Module Export Syntax. 
Notation "[ 'Event' 'of' p ]" := (lfsposet_lposetType p)
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


Module Hom.
Section Hom.
Context {E1 E2 : identType} {L : eqType} {bot : L}.
Variables (p : lfsposet E1 L bot) (q : lfsposet E2 L bot).
Implicit Types (f : [Event of p] -> [Event of q]).
Implicit Types (ff : { ffun [FinEvent of p] -> [FinEvent of q] 
                     | lFinPoset.hom_pred }).

Definition lift (ff : [FinEvent of p] -> [FinEvent of q]) : 
  [Event of p] -> [Event of q] := 
    sub_lift (fun=> fresh_seq (finsupp q)) (fun e => val (ff e)).

Definition axiom f := (
                       { mono f : e     / lab e    }  *
    {in (finsupp p) &, { homo f : e1 e2 / e1 <= e2 }}
  )%type.

(* TODO: think about better naming convention for this 
 *   and the following lemmas 
 *)
Lemma hom_axiom ff : axiom (lift ff).
Proof.
  pose f := lFinPoset.hom_of_fhom ff.
  rewrite /lift; constructor. 
  - move=> e; rewrite !fs_labE.
    case: (e \in finsupp p)/idP=> [eIn|/negP eNIn]; last first.
    + rewrite sub_liftF // ?fs_lab_bot //; last exact/negP.
      exact/fresh_seq_nmem. 
    rewrite sub_liftT=> //=.
    have{2}->: e = val (Sub e eIn : [FinEvent of p]) by done.
    rewrite !fin_lab_mono -fin_labE -fin_labE.
    apply/(lab_preserving f).
  move=> e1 e2; rewrite !fs_caE=> eIn1 eIn2 ca12.
  rewrite !sub_liftT /=; move: ca12.
  have {1}->: e1 = val (Sub e1 eIn1 : [FinEvent of p]) by done.  
  have {1}->: e2 = val (Sub e2 eIn2 : [FinEvent of p]) by done.  
  rewrite !fin_ca_mono -fin_caE -fin_caE.
  exact/(ca_monotone f).
Qed.

Lemma hom_in_finsupp f e : 
  axiom f -> e \in finsupp p -> (f e) \in finsupp q.
Proof. 
  move=> ax /[dup] eIn. 
  by rewrite -fs_labNbot -fs_labNbot -fs_labE -fs_labE ax.
Qed.

(* TODO: rename? *)
Definition restr f (ax : axiom f) : 
  {ffun [FinEvent of p] -> [FinEvent of q]} :=
    [ffun e => [` hom_in_finsupp ax (valP e)] ].  

Lemma hom_pred_of_hom f (ax : axiom f) : 
  lFinPoset.hom_pred (restr ax).
Proof. 
  rewrite /restr /lFinPoset.hom_pred. 
  apply/andP; split.
  - apply/fin_lab_preservingP=> e.
    rewrite !fin_labE /fin_lab /= !ffunE -fs_labE -fs_labE //=. 
    by rewrite ax.
  apply/fin_ca_monotoneP=> e1 e2.
  rewrite !fin_caE -fin_ca_mono -fin_ca_mono !ffunE -fs_caE -fs_caE /=. 
  by move=> ?; rewrite ax.
Qed.

(* TODO: make canonical? *)
Definition fhom_of f (ax : axiom f) : 
  {ffun [FinEvent of p] -> [FinEvent of q] | lFinPoset.hom_pred} := 
    Sub (restr ax) (hom_pred_of_hom ax).

End Hom.

Arguments  Hom.axiom {_ _ _ _} _ _.

(* TODO: rename to PreOrder? *)
Module Theory.
Section Theory.
Context {E : identType} {L : eqType} {bot : L}.
Implicit Types (p q : lfsposet E L bot).

Lemma hom_operational p q : 
  Hom.axiom p q id -> operational q -> operational p.
Proof.
  (do ? case)=> _ cm /(operationalP (lfsp_supp_closed _) (lfsp_acyclic _)) sb.
  apply/forall2P=> -[/= ? {}/cm cm [/= ? {}/cm cm]].
  by apply/implyP=> /cm/sb.
Qed.

End Theory.
End Theory.

End Hom.

Module iHom.
Section iHom.
Context {E1 E2 : identType} {L : eqType} {bot : L}.
Variables (p : lfsposet E1 L bot) (q : lfsposet E2 L bot).
Implicit Types (f : [Event of p] -> [Event of q]).
Implicit Types (ff : { ffun [FinEvent of p] -> [FinEvent of q] 
                     | lFinPoset.ihom_pred }).

Definition axiom f := 
  { in (finsupp p) &, injective f }.

Lemma fihom_inj ff : 
  axiom (Hom.lift ff).
Proof. 
  pose f := lFinPoset.ihom_of_fihom ff.  
  rewrite /Hom.lift => /= e1 e2 e1In e2In.
  rewrite !sub_liftT=> //=.  
  by move=> /val_inj/(@ihom_inj _ _ _ f)/sub_inj.
Qed.

Lemma ihom_pred_of_ihom f (ax : Hom.axiom p q f): 
  axiom f -> lFinPoset.ihom_pred (Hom.restr ax).
Proof. 
  move=> finj.
  rewrite /lFinPoset.ihom_pred /=.
  apply/andP; split.
  - exact/Hom.hom_pred_of_hom. 
  apply/injectiveP=> e1 e2; rewrite /Hom.restr !ffunE.
  move=> /sub_inj/(finj _ _ (valP e1) (valP e2)); exact/val_inj.
Qed.

End iHom.

Arguments iHom.axiom {_ _ _ _} _ _.

Module PreOrder.
Section hPreOrder.
Context {E1 E2 : identType} {L : eqType} {bot : L}.
Implicit Types (p : lfsposet E1 L bot) (q : lfsposet E2 L bot).

(* TODO: rename bhom_preord? *)
Definition ihom_le p q := 
  let EP := [FinEvent of p] in
  let EQ := [FinEvent of q] in
  ??|{ffun EQ -> EP | lFinPoset.ihom_pred}|.

Lemma ihom_leP p q :
  reflect 
    (exists f, Hom.axiom q p f /\ iHom.axiom q p f)
    (ihom_le p q).
Proof. 
  rewrite /ihom_le; apply/(equivP idP); split.
  - move=> /fin_inhP [] f. 
    pose fi := lFinPoset.fhom_of_fihom f.
    exists (Hom.lift fi); split; first exact/Hom.hom_axiom.
    exact/fihom_inj. 
  move=> [f] [ax finj]; apply/fin_inhP. 
  exists; exists (Hom.restr ax).
  exact/(ihom_pred_of_ihom ax finj).
Qed.

Lemma ihom_le_size p q :
  ihom_le p q -> fs_size q <= fs_size p.
Proof.
  rewrite /ihom_le /fs_size ?cardfE=> /lFinPoset.fihomP[/=] f.
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
Proof. move=> ?; exact/lFinPoset.ihom_refl. Qed.

Lemma ihom_le_trans : transitive (@ihom_le E E L bot). 
Proof. move=> ??? /[swap]; exact/lFinPoset.ihom_trans. Qed.

End PreOrder.
End PreOrder.

End iHom.

Export iHom.PreOrder.

Module bHom.
Section bHom.
Context {E1 E2 : identType} {L : eqType} {bot : L}.
Variables (p : lfsposet E1 L bot) (q : lfsposet E2 L bot).
Implicit Types (f : [Event of p] -> [Event of q]).
Implicit Types (ff : { ffun [FinEvent of p] -> [FinEvent of q] 
                     | lFinPoset.bhom_pred }).

Definition axiom (f : [Event of p] -> [Event of q]) := 
  {on (finsupp q), bijective f}.

Lemma bhom_axiom ff : 
  axiom (Hom.lift ff).
Proof. 
  pose f := lFinPoset.bhom_of_fbhom ff.  
  pose gf := lPoset.bHom.invF f.
  pose g  := Hom.lift gf.
  exists g=> /= e /=; last first. 
  - move=> eIn; rewrite /g /Hom.lift !sub_liftT //= => gIn.
    suff->: (ff.[gIn] = f (gf.[eIn]))%fmap by rewrite can_inv. 
    by rewrite /f /=; f_equal; apply/val_inj=> /=. 
  case: (e \in finsupp p)/idP; last first.
  - move=> nIn; rewrite /Hom.lift sub_liftF=> //.
    by move: (fresh_seq_nmem (finsupp q))=> /negP.
  move=> eIn; rewrite /g /Hom.lift !sub_liftT => //= fIn _.
  suff->: (gf.[fIn] = gf (ff.[eIn]))%fmap by rewrite /gf inv_can.
  by f_equal; apply/val_inj=> /=.
Qed.

Lemma bhom_pred_of_bhom f (ax : Hom.axiom p q f) :
 axiom f -> lFinPoset.bhom_pred (Hom.restr ax).
Proof.
  move=> [g] K K'. 
  rewrite /lFinPoset.bhom_pred /lFinPoset.ihom_pred /=.
  suff fbij: bijective (Hom.restr ax).
  - rewrite -andbA; apply/and3P; split.
    + exact/Hom.hom_pred_of_hom. 
    + exact/injectiveP/bij_inj.
    exact/eq_leq/esym/bij_eq_card/fbij. 
  have suppg : forall e, e \in finsupp q -> (g e) \in finsupp p.
  - move=> e /[dup] eIn; rewrite -fs_labNbot -fs_labNbot -fs_labE -fs_labE. 
    by rewrite -ax; apply/contra; rewrite K'. 
  pose gf : [FinEvent of q] -> [FinEvent of p] := 
    fun e => Sub (g (val e)) (suppg (val e) (valP e)). 
  exists gf=> e; rewrite /gf /Hom.restr ffunE /=. 
  all: apply/val_inj=> //=; rewrite ?K ?K'=> //. 
  exact/Hom.hom_in_finsupp.
Qed.  

End bHom.

Arguments bHom.axiom {_ _ _ _} _ _.

Module PreOrder.
Section hPreOrder.
Context {E1 E2 : identType} {L : eqType} {bot : L}.
Implicit Types (p : lfsposet E1 L bot) (q : lfsposet E2 L bot).

(* TODO: rename bhom_preord? *)
Definition bhom_le p q := 
  let EP := [FinEvent of p] in
  let EQ := [FinEvent of q] in
  ??|{ffun EQ -> EP | lFinPoset.bhom_pred}|.

Lemma bhom_img p q f : 
  Hom.axiom p q f -> {in finsupp p, forall e, (f e) \in finsupp q}.
Proof.
  move=> ax e /[dup] eIn. 
  rewrite -fs_labNbot -fs_labNbot -fs_labE -fs_labE.
  by move=> /eqP labD; apply/eqP; rewrite ax. 
Qed.

Lemma bhom_pre_img p q f e : 
  Hom.axiom p q f -> f e \in finsupp q -> e \in finsupp p.
Proof.
  move=> ax /[dup] eIn. 
  by rewrite -fs_labNbot -fs_labNbot -fs_labE -fs_labE ax.
Qed. 

Lemma bhom_leP p q :
  reflect 
    (exists (f : E2 -> E1), Hom.axiom q p f /\ bHom.axiom q p f)
    (bhom_le p q).
Proof. 
  rewrite /bhom_le; apply/(equivP idP); split.
  - move=> /fin_inhP [] f. 
    pose fi := lFinPoset.fihom_of_fbhom f.
    pose fh := lFinPoset.fhom_of_fihom fi.
    exists (Hom.lift fh); split; first exact/Hom.hom_axiom.
    exact/bhom_axiom.
  case=> f [ax ?]; apply/fin_inhP. 
  exists; exists (Hom.restr ax).
  exact/(bhom_pred_of_bhom ax).
Qed.

Lemma bhom_ihom_le p q : 
  bhom_le p q -> ihom_le p q.
Proof.
  rewrite /bhom_le /ihom_le=> /fin_inhP /= [f]. 
  by apply/fin_inhP/inh_impl; first exact/lFinPoset.fihom_of_fbhom.
Qed.

Lemma bhom_le_size p q :
  bhom_le p q -> fs_size p = fs_size q.
Proof.
  rewrite /bhom_le /fs_size ?cardfE=> /lFinPoset.fbhomP[/=] f.
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

Lemma finsupp_hom_id p q : 
  Hom.axiom q p id -> finsupp p = finsupp q.
Proof.
  move=> /[dup] /bhom_img s1 /bhom_pre_img s2.
  apply/fsetP=>>; apply/idP/idP=> ?; by rewrite (s1, s2).
Qed.

Lemma bhom_lt_def p q : bhom_lt p q = (q != p) && (bhom_le p q).
Proof. done. Qed.

Lemma bhom_le_refl : reflexive (@bhom_le E E L bot). 
Proof. move=> ?; exact/lFinPoset.bhom_refl. Qed.

Lemma bhom_le_trans : transitive (@bhom_le E E L bot). 
Proof. move=> ??? /[swap]; exact/lFinPoset.bhom_trans. Qed.

End PreOrder.
End PreOrder.

End bHom.

Export bHom.PreOrder.

Module Emb.
Section Emb.
Context {E1 E2 : identType} {L : eqType} {bot : L}.
Variables (p : lfsposet E1 L bot) (q : lfsposet E2 L bot).
Implicit Types (f : [Event of p] -> [Event of q]).
Implicit Types (ff : { ffun [FinEvent of p] -> [FinEvent of q] 
                     | lFinPoset.emb_pred }).

Definition axiom (f : [Event of p] -> [Event of q]) := 
  { in finsupp p &, lPoset.Emb.Emb.axiom f }.

Lemma emb_axiom ff : 
  axiom (Hom.lift ff).
Proof. 
  pose f := lFinPoset.emb_of_femb ff.  
  have ffE: forall e, ff e = f e by done.
  move=> e1 e2 e1In e2In. 
  rewrite /Hom.lift !sub_liftT. 
  rewrite !fs_caE /fs_ca /= /dhrel_one /=.
  rewrite !sub_rel_lift_val /sub_rel_lift /= !insubT=> H.
  suff: (fin_ca q (ff.[e1In]) (ff.[e2In]))%fmap. 
  - rewrite !ffE -fin_caE -fin_caE (ca_reflecting f). 
    by move=> ?; apply/orP; right. 
  move: H=> /orP[/eqP/val_inj->|] //.
  exact/fin_ca_refl.
Qed.

Lemma emb_pred_of_emb f (ax : Hom.axiom p q f) : 
  axiom f -> lFinPoset.emb_pred (Hom.restr ax).
Proof.
  rewrite /axiom=> /= femb.
  rewrite /lFinPoset.emb_pred /=.
  apply/andP; split.
  - exact/Hom.hom_pred_of_hom. 
  apply/forall2P=> e1 e2; apply/implyP.
  rewrite /Hom.restr !ffunE fin_caE -fin_ca_mono /=.
  move=> /femb H; move: (H (valP e1) (valP e2)); clear H.
  rewrite fs_caE /fs_ca /= sub_rel_lift_val=> /orP[|] //=. 
  move=> /eqP/val_inj->; exact/fin_ca_refl.
Qed.

End Emb.

Arguments Emb.axiom {_ _ _ _} _ _.

Module PreOrder.
Section hPreOrder.
Context {E1 E2 : identType} {L : eqType} {bot : L}.
Implicit Types (p : lfsposet E1 L bot) (q : lfsposet E2 L bot).

Definition emb_le p q := 
  let EP := [FinEvent of p] in
  let EQ := [FinEvent of q] in
  ??|{ffun EQ -> EP | lFinPoset.emb_pred}|.

Lemma emb_leP p q :
  reflect 
    (exists (f : [Event of q] -> [Event of p]), Hom.axiom q p f /\ axiom q p f)
    (emb_le p q).
Proof. 
  rewrite /emb_le; apply/(equivP idP); split.
  - move=> /fin_inhP [] f. 
    pose fh := lFinPoset.fhom_of_femb f.
    exists (Hom.lift fh); split; first exact/Hom.hom_axiom.
    exact/emb_axiom. 
  move=> [f [ax ?]] ; apply/fin_inhP. 
  exists; exists (Hom.restr ax).
  exact/(emb_pred_of_emb ax).
Qed.

Lemma emb_ihom_le p q : 
  emb_le p q -> ihom_le p q.
Proof.
  rewrite /emb_le /ihom_le=> /fin_inhP [f]. 
  apply/fin_inhP/inh_impl; last first.
  - exists; exact/f.
  move=> {}f; pose f' := lFinPoset.emb_of_femb f.
  apply/lFinPoset.fihom_of_ihom; exact/f'.
Qed.

Lemma emb_le_size p q :
  emb_le p q -> fs_size q <= fs_size p.
Proof. by move=> /emb_ihom_le /ihom_le_size. Qed.

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
Proof. move=> ?; exact/lFinPoset.emb_refl. Qed.

Lemma emb_le_trans : transitive (@emb_le E E L bot). 
Proof. move=> ??? /[swap]; exact/lFinPoset.emb_trans. Qed.

End PreOrder.
End PreOrder.

End Emb.

Export Emb.PreOrder.

Module Export Iso.
Section Iso.
Context {E1 E2 : identType} {L : eqType} {bot : L}.
Variables (p : lfsposet E1 L bot) (q : lfsposet E2 L bot).
Implicit Types (f : [Event of p] -> [Event of q]).
Implicit Types (ff : { ffun [FinEvent of p] -> [FinEvent of q] 
                     | lFinPoset.iso_pred }).

Lemma hom_axiom ff :
  Hom.axiom p q (Hom.lift ff).
Proof.
  pose f := 
     lFinPoset.fhom_of_fihom 
    (lFinPoset.fihom_of_fbhom 
    (lFinPoset.fbhom_of_fiso ff)).
  have->: Hom.lift ff = Hom.lift f by done.
  exact(@Hom.hom_axiom _ _ _ _ _ _ f).
Qed.

Lemma bhom_axiom ff : 
  bHom.axiom p q (Hom.lift ff).
Proof. 
  pose fb := lFinPoset.fbhom_of_fiso ff.
  have->: Hom.lift ff = Hom.lift fb by done.
  exact(@bHom.bhom_axiom _ _ _ _ _ _ fb).
Qed.
  
Lemma emb_axiom ff : 
  Emb.axiom p q (Hom.lift ff).
Proof. 
  pose fe := lFinPoset.femb_of_fiso ff.
  have->: Hom.lift ff = Hom.lift fe by done. 
  exact(@Emb.emb_axiom _ _ _ _ _ _ fe).
Qed.

Lemma iso_pred_of_iso f (ax : Hom.axiom p q f): 
  bHom.axiom p q f -> Emb.axiom p q f -> lFinPoset.iso_pred (Hom.restr ax).
Proof. 
  move=> bhom_ax emb_ax.
  rewrite /lFinPoset.iso_pred /=.
  apply/andP; split.
  - exact/bHom.bhom_pred_of_bhom. 
  by move: (Emb.emb_pred_of_emb ax emb_ax) => /andP[]. 
Qed.

End Iso.

Module Equiv.
Section hEquiv.
Context {E1 E2 : identType} {L : eqType} {bot : L}.
Implicit Types (p : lfsposet E1 L bot) (q : lfsposet E2 L bot).

Definition iso_eqv p q := 
  let EP := [FinEvent of p] in
  let EQ := [FinEvent of q] in
  ??|{ffun EQ -> EP | lFinPoset.iso_pred}|.

Lemma iso_eqvP p q :
  reflect 
    (exists (f : [Event of q] -> [Event of p]), 
      [/\ Hom.axiom q p f, bHom.axiom q p f & Emb.axiom q p f])
    (iso_eqv p q).
Proof. 
  rewrite /iso_eqv; apply/(equivP idP); split.
  - move=> /fin_inhP [] f. 
    pose fe := lFinPoset.femb_of_fiso f.
    pose fh := lFinPoset.fhom_of_femb fe.
    exists (Hom.lift fh).
    split; [exact/hom_axiom| exact/bhom_axiom | exact/emb_axiom]. 
  move=> [f] [] ax fbij femb; apply/fin_inhP. 
  exists; exists (Hom.restr ax).
  exact/(iso_pred_of_iso ax).
Qed.

Lemma iso_bhom_le p q : 
  iso_eqv p q -> bhom_le p q.
Proof.
  rewrite /iso_eqv /bhom_le=> /fin_inhP [f]. 
  pose f' := lFinPoset.fbhom_of_fiso f.
  apply/fin_inhP; exists; exact/f'.
Qed.

Lemma iso_emb_le p q : 
  iso_eqv p q -> emb_le p q.
Proof.
  rewrite /iso_eqv /emb_le=> /fin_inhP [f]. 
  pose f' := lFinPoset.femb_of_fiso f.
  apply/fin_inhP; exists; exact/f'.
Qed.

Lemma iso_ihom_le p q : 
  iso_eqv p q -> ihom_le p q.
Proof. by move=> /iso_bhom_le /bhom_ihom_le. Qed.

Lemma iso_eqv_size p q :
  iso_eqv p q -> fs_size p = fs_size q.
Proof. by move=> /iso_bhom_le /bhom_le_size. Qed.

Lemma bhom_factor p q : 
  bhom_le p q -> 
    exists2 q' : lfsposet E1 L bot, 
      iso_eqv q' q &
      Hom.axiom q' p id.
Proof.
  case/bhom_leP=> f [ax [g c1 c2]].
  set fE := finsupp p.
  set lab : fE -> L := fun e => lab (g (val e)).
  set ca  : rel E1  := fun e1 e2 => 
    (e1 == e2) || 
    [&& fs_ca q (g e1) (g e2), e1 \in finsupp p & e2 \in finsupp p].
  have [: a1 a2 a3 a4] @q' := 
    @lFsPoset.build_cov E1 L bot fE lab ca a1 a2 a3 a4.
  - by case=> ??; rewrite /lab /= -ax c2 // fs_labE fs_labNbot.
  - by move=> ?; rewrite /ca eqxx.
  - move=>> /andP[] /orP[/eqP-> //|/and3P[+ ??]].
    move/ax.2; rewrite ?(bhom_pre_img ax) ?c2 // =>/(_ erefl erefl)/[swap].
    case/orP=>[/eqP->//|/and3P[+??]].
    move/ax.2; rewrite ?(bhom_pre_img ax) ?c2 // =>/(_ erefl erefl)/[swap].
    move=> l1 l2; apply/(fs_ca_antisym (lfsp_supp_closed p) (lfsp_acyclic p)).
    exact/andP.
  - set ft := (fs_ca_trans (lfsp_supp_closed q)).
    move=>>; rewrite /ca => /orP[/eqP->//|/and3P[/[dup] fc /ft tr i1 i2]].
    move/orP=>[/eqP<-|]; rewrite ?fc ?i1 i2 //=.
    by move/andP=> [/tr->]->.
  exists q'; first (apply/iso_eqvP=> /=; exists f); repeat split.
  - move=> x; rewrite ?fs_labE ?/(_ <= _) /=.
    rewrite lFsPrePoset.build_lab /sub_lift.
    case: insubP=> /=; rewrite /lab.
    + by case=> /= ???->; rewrite c1.
      move: (ax.1 x); rewrite -fs_labNbot ?fs_labE=>->.
      by rewrite negbK=> /eqP. 
    move=>>??; rewrite ?/(_ <= _) /= lFsPrePoset.build_cov_ca // /ca.
    by rewrite ?c1 ?(bhom_img ax) // =>->; lattice.
  - by exists g; rewrite lFsPrePoset.build_finsupp.
  - move=> x y ??. 
    have fxy: f x == f y -> x = y.
    + move/eqP/(congr1 g); rewrite ?c1 ?(bhom_img ax) //.
    rewrite ?/(_ <= _) /= lFsPrePoset.build_cov_ca // /ca.
    case/orP=> [/fxy->|]; first exact/fs_ca_refl.
    case/and3P=>/orP[/fxy->*|]; first exact/fs_ca_refl.
    by case/and3P=>+??; rewrite ?c1.
  - move=> e; rewrite ?fs_labE lFsPrePoset.build_lab /sub_lift.
    case: insubP=> /= [[/=>?]|].
    - rewrite /lab -ax.1 fs_labE /= c2 // =>-> //.
    by rewrite -fs_labNbot negbK=>/eqP->.
  move=>>; rewrite ?/(_ <= _) /= lFsPrePoset.build_cov_ca // /ca /fE.
  rewrite lFsPrePoset.build_finsupp // => ??.
  case/orP=> [/eqP->|]; first exact/fs_ca_refl.
  case/and3P=> /orP[/eqP->*|]; first exact/fs_ca_refl.
  by case/and3P=> /ax.2; rewrite ?(bhom_pre_img ax) ?c2 // /(_ <= _) /==>->.
Qed.

End hEquiv.

Section Equiv.
Context (E : identType) (L : eqType) (bot : L).
Implicit Types (p q : lfsposet E L bot).

(* TODO: generalize the proofs to arbitary `T -> T -> Type`? *)
Lemma iso_eqv_refl : reflexive (@iso_eqv E E L bot).
Proof. 
  rewrite /iso_eqv=> p.
  apply/lFinPoset.fisoP. 
  exists; exact/[iso of idfun]. 
Qed.

Lemma iso_eqv_sym : symmetric (@iso_eqv E E L bot).
Proof. 
  rewrite /iso_eqv=> p q.
  apply/idP/idP=> /lFinPoset.fisoP [f]; 
    apply/lFinPoset.fisoP; 
    (* TODO: [iso of ...] notation for inverse *)
    exists; exact/(lPoset.Iso.Build.inv f).
Qed.

Lemma iso_eqv_trans : transitive (@iso_eqv E E L bot).
Proof. 
  rewrite /iso_eqv=> p q r.
  move=> /lFinPoset.fisoP [f] /lFinPoset.fisoP [g]. 
  apply/lFinPoset.fisoP. 
  exists; exact/[iso of f \o g].
Qed.

Lemma iso_ihom_le_antisym p q : 
  ihom_le p q -> ihom_le q p -> iso_eqv p q.
Proof.
  move=> /lFinPoset.fihomP[f] /lFinPoset.fihomP[g].
  apply/lFinPoset.fisoP; exists; exact/(lFinPoset.of_ihoms f g).
Qed.

Lemma iso_bhom_le_antisym p q : 
  bhom_le p q -> bhom_le q p -> iso_eqv p q.
Proof. move=> /bhom_ihom_le + /bhom_ihom_le; exact/iso_ihom_le_antisym. Qed.

Lemma iso_emb_le_antisym p q : 
  emb_le p q -> emb_le q p -> iso_eqv p q.
Proof. move=> /emb_ihom_le + /emb_ihom_le; exact/iso_ihom_le_antisym. Qed.

End Equiv.
End Equiv.

End Iso.

Export Iso.Equiv.

End lFsPoset.

Export lFsPoset.Def.
Export lFsPoset.Instances.
Export lFsPoset.Syntax.
Export lFsPoset.Theory.
Export lFsPoset.Hom.Theory.
Export lFsPoset.iHom.PreOrder.
Export lFsPoset.bHom.PreOrder.
Export lFsPoset.Emb.PreOrder.
Export lFsPoset.Iso.Equiv.

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

Variables (f : L1 -> L2) (p : lfsposet E L1 bot1).
Hypothesis (fbot : f bot1 = bot2).
Hypothesis (flabD : [forall e : finsupp p, f (fs_lab p (val e)) != bot2]).

Definition relabel : pomset E L2 bot2 := 
  \pi (@lFsPoset.relabel E L1 L2 bot1 bot2 f p fbot flabD).

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
  case: pomP=> q' /eqmodP/lFinPoset.fisoP[f]. 
  case: pomP=> p' /eqmodP/lFinPoset.fisoP[g].
  apply/lFinPoset.fihomP/lFinPoset.fihomP=> [][h]; exists. 
  - (* TODO: fix bug with canonical instance inference *)
    pose f' := lPoset.Iso.Build.inv f : {ihom _ -> _}.
    pose g' := g : {ihom _ -> _}.
    exact/[ihom of g' \o h \o f'].
  (* TODO: fix bug with canonical instance inference *)
  pose f' := f : {ihom _ -> _}.
  pose g' := lPoset.Iso.Build.inv g : {ihom _ -> _}. 
  exact/[ihom of g' \o h \o f'].
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
  case: pomP=> q' /eqmodP/lFinPoset.fisoP[f]. 
  case: pomP=> p' /eqmodP/lFinPoset.fisoP[g].
  apply/lFinPoset.fbhomP/lFinPoset.fbhomP=> [][h]; exists.
  - exact/[bhom of g \o h \o lPoset.Iso.Build.inv f].
  exact/[bhom of lPoset.Iso.Build.inv g \o h \o f].
Qed.

Context {E : identType} {L : choiceType} {bot : L}.
Implicit Types (p q : pomset E L bot). 

Lemma pom_bhom_mono :
  {mono (@pom E L bot) : p q / bhom_le p q >-> bhom_le (repr p) (repr q)}.
Proof. exact/pom_bhom_le. Qed.

Canonical bhom_le_quot_mono2 := PiMono2 pom_bhom_mono.

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
  move: (iso_eqv_pom p)=> /lFinPoset.fisoP [f]. 
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
    move=> Hca; apply/orP; right.
    rewrite !conseq_num_mem // /f !decodeK usz !lfsp_idx_lt_szE.
    apply/and3P; split=> //. 
    rewrite ident_leE !decodeK; exact/lfsp_idx_le.
  - pose g : [Event of u] -> [Event of t] := 
      fun e => lfsp_event t \i0 (encode e).
    exists g=> e; rewrite !conseq_num_mem // /f /g !usz ?decodeK.
    + rewrite lfsp_idx_lt_szE; exact/lfsp_idxK. 
    by move=> ?; rewrite lfsp_eventK ?encodeK //. 
  move=> e1 e2 e1In e2In; rewrite /f fs_caE /=.
  rewrite lFsPoset.of_seq_caE labD andbT //.
  rewrite !conseq_num_mem // !decodeK !usz !lfsp_idx_lt_szE.
  rewrite ident_leE !decodeK=> /orP[/eqP|].
  - move=> /decode_inj /lfsp_idx_inj -> //; exact/fs_ca_refl.
  move=> /and3P[le12 ??].  
  move: (tomset_total_in e1In e2In).  
  rewrite !fs_caE=> /orP[|] //.
  move=> /lfsp_idx_le le21.
  suff->: e1 = e2 by exact/fs_ca_refl.
  apply/(lfsp_idx_inj e1In e2In).
  by apply/le_anti/andP. 
Qed.

End Theory.
End Theory.

End Tomset.

Export Tomset.Def.
Export Tomset.Theory.
