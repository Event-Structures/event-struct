From Coq Require Import Relations.
From RelationAlgebra Require Import lattice monoid rel fhrel boolean kat_tac.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat seq tuple.
From mathcomp Require Import eqtype choice order generic_quotient.
From mathcomp Require Import fintype finfun finset fingraph finmap zify.
From mathcomp.tarjan Require Import extra acyclic kosaraju acyclic_tsorted. 
From eventstruct Require Import utils seq fperm rel rel_algebra inhtype.
From eventstruct Require Import order ident ilia fsrel fsgraph.

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

Local Open Scope rel_scope.
Local Open Scope order_scope.
Local Open Scope fset_scope.
Local Open Scope quotient_scope.
Local Open Scope ra_terms.
Local Open Scope ident_scope.
Local Open Scope fsrel_scope.
Local Open Scope fsgraph_scope.

Declare Scope pomset_scope.
Delimit Scope pomset_scope with pomset.

Local Open Scope pomset_scope.

(* Notation lfspreposet E L bot :=  *)
(*   ({ fsfun E -> (L * {fset E}) of e => (bot, fset0) }). *)

Module lFsPrePoset.

Module Export Def.
Section Def.
Context (E : identType) (L : botType).

(* Definition lfspreposet := *)
(*   { fsfun E -> (L * {fset E}) of e => (bot, fset0) }. *)

Record lfspreposet := mk_fsgraph {
  lfspreposet_val : fsgraph E L;
  _ : [&& fsrel_irreflexive (edges lfspreposet_val)
        &  fsrel_transitive (edges lfspreposet_val)
      ];
}.

Canonical lfspreposet_subType := Eval hnf in [subType for lfspreposet_val].

Implicit Types (p : lfspreposet).

Coercion fsgraph_of_lfspreposet p : fsgraph E L := 
  lfspreposet_val p.

Definition lfspreposet_eqMixin := 
  Eval hnf in [eqMixin of lfspreposet by <:].
Canonical lfspreposet_eqType := 
  Eval hnf in EqType lfspreposet lfspreposet_eqMixin.

Definition lfspreposet_choiceMixin := 
  Eval hnf in [choiceMixin of lfspreposet by <:].
Canonical lfspreposet_choiceType := 
  Eval hnf in ChoiceType lfspreposet lfspreposet_choiceMixin.

Definition ca p : rel E := 
  (edges p : {hrel E & E})^?.

Definition sca p : rel E := 
  edges p.

(* Definition lfsp_size p : nat := #|` lfsp_eventset p|. *)

(* Definition lfsp_tseq p : seq E := *)
(*   map val (tseq (rgraph (@fin_ica p))). *)

(* Definition lfsp_idx p : E -> nat := *)
(*   fun e => index e (lfsp_tseq p). *)

(* Definition lfsp_event p e0 : nat -> E := *)
(*   fun n => nth e0 (lfsp_tseq p) n. *)

(* Definition lfsp_labels p : seq L := *)
(*   map (fs_lab p) (lfsp_tseq p). *)

(* Definition lfsp_fresh p : E := *)
(*   fresh_seq (lfsp_eventset p). *)

(* Definition conseq_num p := *)
(*   lfsp_eventset p == [fset e | e in nfresh \i0 (lfsp_size p)]. *)

(* Definition lfsp_pideal p e : {fset E} := *)
(*   [fset e' in (e |` lfsp_eventset p) | fs_ca p e' e]. *)

(* (* TODO: unify with UpFinPOrder *) *)
(* Definition lfsp_dw_clos p es := *)
(*   [seq e <- lfsp_eventset p | [exists e' : es, fs_ca p e (val e')]]. *)

(* (* TODO: unify with UpFinPOrder *) *)
(* Definition lfsp_is_maximal p e := *)
(*   [forall e' : lfsp_eventset p, (fs_ca p e (val e')) ==> (fs_ca p (val e') e)]. *)

(* (* TODO: unify with UpFinPOrder *) *)
(* Definition lfsp_is_greatest p e := *)
(*   [forall e' : lfsp_eventset p, fs_ca p (val e') e]. *)

(* Definition lfsp_equiv_partition p r : {fset {fset E}} := *)
(*   let part := equivalence_partition r [set: lfsp_eventset p] in *)
(*   [fset [fset (val e) | e : lfsp_eventset p & (e \in (P : {set _}))] | P in part]. *)

(* (* TODO: move/restructure *) *)
(* Context (L' : botType). *)
(* Implicit Types (f : L -> L'). *)

(* Definition finsupp_preserving p f := *)
(*   [forall e : lfsp_eventset p, f (fs_lab p (val e)) != bot]. *)

End Def.

(* Arguments fs_ica {E L} p. *)
Arguments ca  {E L} p.
Arguments sca {E L} p.

End Def.

Arguments lfspreposet E L : clear implicits.

Module Export Theory.
Section Theory.
Context (E : identType) (L : botType).
Implicit Types (p q : lfspreposet E L) (ls : seq L).

(* ************************************************************************** *)
(*     Switching between finType <-> finsupp                                  *)
(* ************************************************************************** *)

(* Lemma fin_lab_mono p : *)
(*   {mono val : e / fin_lab p e >-> fs_lab p e}. *)
(* Proof. done. Qed. *)

(* Lemma fin_ica_mono p : *)
(*   {mono val : x y / fin_ica p x y >-> fs_ica p x y}. *)
(* Proof. done. Qed. *)

(* Lemma fin_ca_mono p : *)
(*   {mono val : x y / fin_ca p x y >-> fs_ca p x y}. *)
(* Proof. *)
(*   move=> e1 e2; rewrite /fs_ca dhrel_qmkE /=. *)
(*   rewrite /sub_rel_lift /=. *)
(*   case: insubP; last first. *)
(*   - by move: (valP e1)=> + /negP. *)
(*   case: insubP; last first. *)
(*   - by move: (valP e2)=> + /negP. *)
(*   move=> e1' in1 /val_inj <- e2' in2 /val_inj <-. *)
(*   rewrite orb_idl // => /eqP/val_inj ->. *)
(*   exact/connect_refl. *)
(* Qed. *)

(* ************************************************************************** *)
(*     Basic properties                                                       *)
(* ************************************************************************** *)

Lemma sca_irrefl p :
  irreflexive (sca p).
Proof. by move: (valP p)=> /andP[] /fsrel_irreflexiveP. Qed.

(* covered by fsgraphP *)
(* Lemma lfspreposet_eqP p q : *)
(*   reflect ((fs_lab p =1 fs_lab q) * (fs_ica p =2 fs_ica q)) (p == q). *)
(* Proof. *)
(*   apply/(equivP idP); split=> [/eqP->|[]] //. *)
(*   rewrite /fs_lab /fs_ica=> eq_lab eq_ica. *)
(*   apply/eqP/fsfunP=> e /=; apply/eqP. *)
(*   rewrite /eq_op=> /=; apply/andP; split. *)
(*   - by rewrite (eq_lab e). *)
(*   apply/fset_eqP=> e'. *)
(*   move: (eq_ica e' e)=> /=. *)
(*   by rewrite /fs_rcov. *)
(* Qed. *)

Lemma ca_refl p :
  reflexive (ca p).
Proof. exact/qmk_refl. Qed.

(* TODO: move *)
(* Lemma fs_ca_antisym p : *)
(*   acyclic (fin_ica p) -> antisymmetric (fs_ca p). *)
(* Proof. move=> asym; exact/qmk_antisym/sub_rel_lift_antisym/acyc_antisym. Qed. *)

Lemma sca_trans p :
  transitive (sca p).
Proof. by move: (valP p)=> /andP[] ? /fsrel_transitiveP. Qed.

Lemma ca_trans p :
  transitive (ca p).
Proof. exact/qmk_trans/sca_trans. Qed.

Lemma scaE p x y :
  sca p x y = (y != x) && (ca p x y).
Proof. 
  rewrite /ca /sca dhrel_qmkE /=.
  rewrite andb_orr eq_sym andNb /=. 
  apply/idP/idP=> [|/andP[]] // /[dup]. 
  by move: (sca_irrefl p)=> /irrefl_neq /[apply] ->.
Qed.

Lemma ca_scaE p x y :
  ca p x y = (x == y) || (sca p x y).
Proof. done. Qed.


(* Lemma fin_caP p e1 e2 : *)
(*   reflect (clos_refl_trans (fin_ica p) e1 e2) (fin_ca p e1 e2). *)
(* Proof. *)
(*   apply/equivP. *)
(*   - exact/connect_strP. *)
(*   by rewrite clos_rt_str. *)
(* Qed. *)

(* Lemma fin_scaP p e1 e2 : *)
(*   reflect (e2 != e1 /\ clos_trans (fin_ica p) e1 e2) (fin_sca p e1 e2). *)
(* Proof. *)
(*   apply/(equivP (andPP _ _)). *)
(*   - exact/idP. *)
(*   - exact/fin_caP. *)
(*   rewrite clos_rt_str clos_t_itr str_itr; split. *)
(*   - by move=> [] /negP ? [/eqP|] //=; rewrite eq_sym. *)
(*   move=> [] neq tr; split=> //; by right. *)
(* Qed. *)

(* Lemma fin_ica_irrefl p : *)
(*   irreflexive (fs_ica p) -> irreflexive (fin_ica p). *)
(* Proof. *)
(*   move=> irr; apply/irreflexive_mono. *)
(*   - exact/fin_ica_mono. *)
(*   move=> /= *; exact/irr. *)
(* Qed. *)

(* Lemma fin_ca_antisym p : *)
(*   antisymmetric (fs_ca p) -> antisymmetric (fin_ca p). *)
(* Proof. *)
(*   move=> asym; apply/antisymmetric_mono. *)
(*   - exact/fin_ca_mono. *)
(*   move=> x y /= ?; exact/val_inj/asym. *)
(* Qed. *)

(* ************************************************************************** *)
(*     Lab and eventset lemmas                                                *)
(* ************************************************************************** *)

(*  mem_nodes *)
(* Lemma fs_labNbotE p e :  *)
(*   (fs_lab p e != bot) = (e \in lfsp_eventset p). *)
(* Proof. *)
(*   rewrite /lfsp_eventset !inE /fs_lab andb_idl ?mem_finsupp //=. *)
(*   by case: (p e)=> l es; rewrite xpair_eqE negb_and /= => ->. *)
(* Qed. *)

(* memNnodes *)
(* Lemma fs_lab_botE p e :  *)
(*   (fs_lab p e == bot) = (e \notin lfsp_eventset p). *)
(* Proof. by rewrite -fs_labNbotE negbK. Qed.   *)

(* Lemma fs_lab_bot p e : *)
(*   (e \notin lfsp_eventset p) -> fs_lab p e = bot. *)
(* Proof. by rewrite -fs_lab_botE=> /eqP. Qed. *)

(* Lemma eventset_fsupp p : *)
(*   lfsp_eventset p `<=` finsupp p. *)
(* Proof. by apply/fsubsetP=> e; rewrite inE=> /andP[]. Qed. *)

(* ************************************************************************** *)
(*     Properties of topological sorting and event enumeration                *)
(* ************************************************************************** *)

(* Lemma lfsp_tseq_size p : *)
(*   size (lfsp_tseq p) = lfsp_size p. *)
(* Proof. by rewrite /lfsp_tseq /lfsp_size size_map size_tseq cardfE. Qed. *)

(* Lemma mem_lfsp_tseq p : *)
(*   lfsp_tseq p =i lfsp_eventset p. *)
(* Proof. *)
(*   rewrite /lfsp_tseq=> e. *)
(*   apply/idP/idP. *)
(*   - by move=> /mapP [e'] + ->; case: e'. *)
(*   move=> in_supp; apply/mapP. *)
(*   exists (Sub e in_supp)=> //. *)
(*   by rewrite mem_tseq fintype.mem_enum. *)
(* Qed. *)

(* Lemma lfsp_tseq_uniq p : *)
(*   uniq (lfsp_tseq p). *)
(* Proof. rewrite /lfsp_tseq (map_inj_uniq val_inj); exact/tseq_uniq. Qed. *)


(* Lemma lfsp_idx_lt_szE p e : *)
(*   (lfsp_idx p e < lfsp_size p)%N = (e \in lfsp_eventset p). *)
(* Proof. by rewrite /lfsp_idx -lfsp_tseq_size index_mem mem_lfsp_tseq. Qed. *)

(* Lemma lfsp_idx_le_sz p e : *)
(*   lfsp_idx p e <= lfsp_size p. *)
(* Proof. rewrite /lfsp_idx -lfsp_tseq_size; exact/index_size. Qed. *)

(* Lemma lfsp_idxK p e0 : *)
(*   {in lfsp_eventset p, cancel (lfsp_idx p) (lfsp_event p e0)}. *)
(* Proof. *)
(*   rewrite /lfsp_idx /lfsp_event=> e eIn. *)
(*   by rewrite nth_index ?mem_lfsp_tseq. *)
(* Qed. *)

(* Lemma lfsp_eventK p e0 : *)
(*   {in (< lfsp_size p), cancel (lfsp_event p e0) (lfsp_idx p)}. *)
(* Proof. *)
(*   rewrite /lfsp_idx /lfsp_event=> n. *)
(*   rewrite inE ltEnat=> nLe. *)
(*   rewrite index_uniq ?lfsp_tseq_size //. *)
(*   exact/lfsp_tseq_uniq. *)
(* Qed. *)

(* Lemma lfsp_idx_inj p : *)
(*   {in lfsp_eventset p &, injective (lfsp_idx p)}. *)
(* Proof. *)
(*   rewrite /lfsp_idx=> e1 e2 e1In e2In. *)
(*   by apply/index_inj; rewrite mem_lfsp_tseq. *)
(* Qed. *)

(* Lemma lfsp_idx_le p e1 e2 : acyclic (fin_ica p) -> *)
(*   fs_ca p e1 e2 -> (lfsp_idx p e1 <= lfsp_idx p e2)%N. *)
(* Proof. *)
(*   move=> acyc. *)
(*   rewrite /lfsp_idx /lfsp_tseq /fs_ca /=. *)
(*   move=> /orP[/eqP->|]; first exact/leqnn. *)
(*   rewrite /sub_rel_lift /=. *)
(*   case: insubP=> // e1' e1In <-. *)
(*   case: insubP=> // e2' e2In <-. *)
(*   rewrite !index_map; try exact/val_inj. *)
(*   move: (tseq_correct (rgraph (fin_ica p)))=> [tc tin]. *)
(*   pose g := grel (rgraph (fin_ica p)). *)
(*   have gE: g =2 (fin_ica p). *)
(*   - by move=> x y /=; rewrite /grel /rgraph fintype.mem_enum. *)
(*   move=> ca12; apply/(@acyclic_connect_before _ g)=> //. *)
(*   - by rewrite (eq_acyclic gE). *)
(*   by rewrite (eq_connect gE). *)
(* Qed. *)

(* Lemma lfsp_labels_size p : *)
(*   size (lfsp_labels p) = lfsp_size p. *)
(* Proof. by rewrite /lfsp_labels size_map lfsp_tseq_size. Qed. *)

(* Lemma lfsp_labels_Nbot p : *)
(*   bot \notin lfsp_labels p. *)
(* Proof. *)
(*   rewrite /lfsp_labels. *)
(*   apply/mapP=> [[e]]. *)
(*   rewrite mem_lfsp_tseq -fs_labNbotE eq_sym.  *)
(*   by move=> /negP + /eqP. *)
(* Qed. *)

(* (* TODO: fs_lab p e = nth bot (lfsp_labels p) (encode p e) ?? *) *)
(* Lemma fs_lab_nthE p e : *)
(*   fs_lab p e = nth bot (lfsp_labels p) (lfsp_idx p e). *)
(* Proof. *)
(*   rewrite /lfsp_labels /lfsp_idx. *)
(*   case: (e \in lfsp_eventset p)/idP=> [eIn | /negP enIn]. *)
(*   - by rewrite (nth_map \i0) ?nth_index ?index_mem ?mem_lfsp_tseq. *)
(*   rewrite nth_default ?fs_lab_bot //. *)
(*   rewrite size_map memNindex ?lfsp_tseq_size //. *)
(*   by rewrite mem_lfsp_tseq. *)
(* Qed. *)

(* Lemma fs_ica_fin_icaE p : supp_closed p -> *)
(*   fs_ica p =2 sub_rel_lift (fin_ica p). *)
(* Proof. *)
(*   move=> sc>; rewrite /fin_ica sub_rel_lift_downK=> //=>. *)
(*   by case/(supp_closedP _ sc)=> /=->. *)
(* Qed. *)

(* Lemma fs_ica_irrefl p : supp_closed p -> *)
(*   irreflexive (fin_ica p) -> irreflexive (fs_ica p). *)
(* Proof. *)
(*   move=> /supp_closedP supcl irr => e. *)
(*   case: (e \in lfsp_eventset p)/idP. *)
(*   - by move=> eIn; move: (irr (Sub e eIn))=> /=. *)
(*   case: (fs_ica p e e)/idP => //. *)
(*   by move=> /supcl []. *)
(* Qed. *)

(* Lemma fin_ica_acyclic p : *)
(*   irreflexive (fin_ica p) -> antisymmetric (fin_ca p) -> acyclic (fin_ica p). *)
(* Proof. *)
(*   move=> irrefl asym; rewrite acyclicE. *)
(*   apply/andP; split; [exact/irreflexiveP | exact/antisymmetricP]. *)
(* Qed. *)

(* Lemma fs_caP p e1 e2 : supp_closed p -> *)
(*   reflect (clos_refl_trans (fs_ica p) e1 e2) (fs_ca p e1 e2). *)
(* Proof. *)
(*   (* TODO: try to simplify proof *) *)
(*   move=> supcl; apply/equivP. *)
(*   - apply/(equivP idP); apply: iff_trans. *)
(*     - by apply/rel_qmk_m. *)
(*     rewrite qmk_weq; last first. *)
(*     - move=> /= x y; rewrite /fs_ca. *)
(*       apply: iff_sym; apply: rwP. *)
(*       apply/sub_rel_liftP. *)
(*     by apply: iff_refl. *)
(*   apply: iff_trans=> /=. *)
(*   - apply: or_iff_compat_l. *)
(*     apply/exists_equiv=> e1'. *)
(*     apply/exists_equiv=> e2'. *)
(*     (* TODO: make lemma? *) *)
(*     have H: forall A1 A2 B C, A1 <-> A2 -> [/\ A1, B & C] <-> [/\ A2, B & C]. *)
(*     - move=> ???? [H1 H2]; split; move=> [???]; split=> //; [exact/H1|exact/H2]. *)
(*     apply/H; apply: iff_sym. *)
(*     apply: iff_trans; last first. *)
(*     - apply: rwP; exact/(connect_strP). *)
(*     by apply/clos_rt_str. *)
(*   (* apply: iff_trans; last first. *) *)
(*   (* - by apply/clos_rt_str. *) *)
(*   move=> /=; split=> [[|[e1' [] e2' []]] |]. *)
(*   - move=> ->; exact/rt_refl. *)
(*   - move=> + <- <-; elim=> //. *)
(*     + move=> ??; exact/rt_step. *)
(*     move=> ??? ? + ?; exact/rt_trans. *)
(*   elim=> //=. *)
(*   - move=> {}e1 {}e2 /[dup] /(supp_closedP _ supcl)[]. *)
(*     move=> Pe1 Pe2 ica; right. *)
(*     exists (Sub e1 Pe1), (Sub e2 Pe2). *)
(*     by split=> //; apply/rt_step. *)
(*   - by move=> ?; left. *)
(*   move=> ??? ? [-> ? [->|] | + ? [|]]. *)
(*   - by left. *)
(*   - move=> [e1' [] e2' []] ???. *)
(*     by right; exists e1', e2'. *)
(*   - move=> [e1' [] e2' []] ??? <-. *)
(*     by right; exists e1', e2'. *)
(*   move=> [e1' [] e2' []] rt12 ??. *)
(*   move=> [e3' [] e4' []] rt34 ??. *)
(*   right; exists e1', e4'; split=> //=. *)
(*   apply/rt_trans; first exact/rt12. *)
(*   suff: e2' = e3'=> [->|] //. *)
(*   apply/val_inj=> /=; congruence. *)
(* Qed. *)

(* Lemma fs_ica_ct_fin_sca p : supp_closed p -> acyclic (fin_ica p) -> *)
(*   clos_trans (fs_ica p) \<= sub_rel_lift (fin_sca p). *)
(* Proof. *)
(*   move=> supcl acyc e1 e2; elim; clear e1 e2. *)
(*   - move=> x y; rewrite /sub_rel_lift /=. *)
(*     move=> /[dup] /(supp_closedP _ supcl) [xIn yIn]. *)
(*     rewrite !insubT /fin_sca /fin_ca /fin_ica=> ica_xy. *)
(*     have: fin_ica p (Sub x xIn) (Sub y yIn). *)
(*     - by rewrite /fin_ica /sub_rel_down /=. *)
(*     move=> fica_xy; apply/andP; split; last first. *)
(*     - by apply/connect1. *)
(*     move: (acyc_irrefl acyc)=> irr. *)
(*     apply/eqP=> eq_xy. *)
(*     move: fica_xy; rewrite eq_xy. *)
(*     by move: (irr (Sub x xIn))=> ->. *)
(*   move=> x y z ? H1 ? H2. *)
(*   apply/sub_rel_lift_trans; last first. *)
(*   - exact/H2. *)
(*   - exact/H1. *)
(*   move=> z' x' y'; rewrite /fin_sca /fin_ca. *)
(*   move=> /andP[/eqP neq_zx Hxz] /andP[/eqP neq_yz Hzy]. *)
(*   apply/andP; split; last first. *)
(*   - apply/connect_trans; [exact/Hxz | exact/Hzy]. *)
(*   apply/eqP=> eq_xy. *)
(*   move: eq_xy Hxz Hzy=> -> ??. *)
(*   suff: x' = z'. *)
(*   - by move: neq_zx=> /[swap]->. *)
(*   move: acyc=> /acyc_antisym antisym. *)
(*   by apply/antisym/andP. *)
(* Qed. *)

(* (* TODO: maybe prove for lfsposet? *) *)
(* Lemma fs_scaP p e1 e2 : supp_closed p -> acyclic (fin_ica p) -> *)
(*   reflect (clos_trans (fs_ica p) e1 e2) (fs_sca p e1 e2). *)
(* Proof. *)
(*   move=> supcl acyc. *)
(*   apply/equivP; last first. *)
(*   - symmetry; apply/clos_t_itr. *)
(*   suff: (fs_ica p : hrel E E)^+ \== !1 \& (fs_ca p : hrel E E). *)
(*   - move=> scaE. *)
(*     apply/equivP; last first. *)
(*     + symmetry; apply/scaE. *)
(*     rewrite /fs_sca /iker eq_sym. *)
(*     apply/(equivP idP); split. *)
(*     + by move=> /andP[] /eqP. *)
(*     by move=> /= [/eqP ??]; apply/andP. *)
(*   rewrite -capC. *)
(*   have->: (fs_ica p : hRel E E)^+ \== (fs_ica p : hRel E E)^+ \\ \1. *)
(*   - apply/weq_spec; split; last by lattice. *)
(*     rewrite -clos_t_itr; move=> x y /= ica_xy; split=> //. *)
(*     move: ica_xy=> /[swap] <-. *)
(*     move=> /(fs_ica_ct_fin_sca supcl acyc). *)
(*     rewrite /sub_rel_lift /=. *)
(*     case: insubP=> // x'. *)
(*     by rewrite /fin_sca /iker eq_refl. *)
(*   suff->: (fs_ca p : hRel E E) \== (fs_ica p : hRel E E)^*. *)
(*   - by symmetry; apply/str_itr_sub_one. *)
(*   rewrite -clos_rt_str. *)
(*   move=> ?? /=; symmetry; apply: rwP; exact/fs_caP. *)
(* Qed. *)

(* Lemma fs_sca_closed p e1 e2 : supp_closed p -> acyclic (fin_ica p) -> *)
(*   fs_sca p e1 e2 -> (e1 \in lfsp_eventset p) * (e2 \in lfsp_eventset p). *)
(* Proof. *)
(*   move=> supcl acyc /(fs_scaP _ _ supcl acyc) /clos_t_itr. *)
(*   suff: (fs_ica p : hrel E E)^+ \<= *)
(*          mem (lfsp_eventset p) \x mem (lfsp_eventset p). *)
(*   - by move=> /[apply] /= /andP[]. *)
(*   etransitivity. *)
(*   - apply kleene.itr_leq=> ??. *)
(*     by apply/supp_closedP. *)
(*   move=> ?? /clos_t_itr; elim=> //=. *)
(*   - move=> ?? [??]; exact/andP. *)
(*   by move=> ??? H1 /andP[??] H2 /andP[??]; apply/andP. *)
(* Qed. *)

(* Lemma fs_ca_closed p e1 e2 : supp_closed p -> acyclic (fin_ica p) -> *)
(*   fs_ca p e1 e2 -> *)
(*     (e1 == e2) || (e1 \in lfsp_eventset p) && (e2 \in lfsp_eventset p). *)
(* Proof. *)
(*   move=> supcl acyc. *)
(*   rewrite fs_ca_scaE=> /orP[/eqP->|]. *)
(*    - by rewrite eq_refl. *)
(*   move=> /(fs_sca_closed supcl acyc) [??]. *)
(*   apply/orP; right; exact/andP. *)
(* Qed. *)

(* Lemma fs_ica_ca p : supp_closed p -> acyclic (fin_ica p) ->  *)
(*   subrel (fs_ica p) (fs_sca p). *)
(* Proof.  *)
(*   move=> supcl acyc x y ica. *)
(*   by apply/(fs_scaP _ _ supcl acyc)/t_step. *)
(* Qed. *)

(* Lemma fs_ica_nsupp p e1 e2 : supp_closed p ->  *)
(*   ((e1 \notin lfsp_eventset p) || (e2 \notin lfsp_eventset p)) ->  *)
(*     ~ fs_ica p e1 e2. *)
(* Proof.  *)
(*   move=> supcl nin /(supp_closedP _ supcl) [].  *)
(*   by move: nin=> /orP[] /negP. *)
(* Qed. *)

(* Lemma fs_ca_nsupp p e1 e2 : supp_closed p -> acyclic (fin_ica p) ->  *)
(*   ((e1 \notin lfsp_eventset p) || (e2 \notin lfsp_eventset p)) ->  *)
(*     fs_ca p e1 e2 -> e1 = e2. *)
(* Proof. *)
(*   move=> supcl acyc /[swap]. *)
(*   move=> /(fs_ca_closed supcl acyc) /orP[/eqP->|] //. *)
(*   by move=> /andP[??] /orP[|] /negP. *)
(* Qed. *)

(* ************************************************************************** *)
(*     Properties of down closure and ideals                                  *)
(* ************************************************************************** *)

(* Lemma lfsp_dw_clos_subs p es : *)
(*   {subset (lfsp_dw_clos p es) <= lfsp_eventset p}. *)
(* Proof. by move=> e; rewrite mem_filter=> /andP[]. Qed. *)

(* Lemma lfsp_pidealP p e e' : supp_closed p -> acyclic (fin_ica p) -> *)
(*   e' \in (lfsp_pideal p e) = (fs_ca p e' e). *)
(* Proof. *)
(*   move=> supcl acyc. *)
(*   rewrite /lfsp_pideal !inE; apply/andb_idl. *)
(*   move=> /(fs_ca_closed supcl acyc). *)
(*   move=> /orP[/eqP->|]; rewrite ?eq_refl //. *)
(*   by move=> /andP[]; rewrite /lfsp_eventset !inE=> ->. *)
(* Qed. *)

(* Lemma lfsp_dw_closP p es e : *)
(*   supp_closed p -> acyclic (fin_ica p) -> es `<=` (lfsp_eventset p) -> *)
(*     reflect (exists2 e', fs_ca p e e' & e' \in es) (e \in lfsp_dw_clos p es). *)
(* Proof. *)
(*   move=> supcl acyc /fsubsetP subs. *)
(*   rewrite mem_filter. *)
(*   apply/(equivP idP); split. *)
(*   - move=> /andP[] /existsP[e'] eCa eIn. *)
(*     exists (val e')=> //; exact/(valP e'). *)
(*   move=> [e'] eCa e'In; apply/andP; split. *)
(*   - by apply/existsP; exists (Sub e' e'In). *)
(*   move: eCa; rewrite fs_ca_scaE=> /orP[/eqP->|]. *)
(*   - exact/subs. *)
(*   (* TODO: looks like it can be proven with weaker assumptions *) *)
(*   by move=> /(fs_sca_closed supcl acyc) ->. *)
(* Qed. *)

(* ************************************************************************** *)
(*     Consequently enumerated preposets                                      *)
(* ************************************************************************** *)

(* Lemma conseq_num_mem p e : *)
(*   conseq_num p -> (e \in lfsp_eventset p) = (encode e < lfsp_size p)%N. *)
(* Proof. *)
(*   move=> /eqP->; rewrite in_fset /=. *)
(*   by rewrite in_nfresh encode0 addn0 /=. *)
(* Qed. *)

End Theory.

(* Section TheoryAux. *)
(* Context (E : identType) (L1 : botType) (L2 : botType). *)
(* Implicit Types (p : lfspreposet E L1). *)
(* Implicit Types (q : lfspreposet E L2). *)

(* Lemma fs_ca_ica_eq p q : supp_closed p -> lfsp_eventset p = lfsp_eventset q -> *)
(*   fs_ica p =2 fs_ica q -> fs_ca p =2 fs_ca q. *)
(* Proof. *)
(*   move=> supclp eqsupp eq_ica e1 e2. *)
(*   have supclq : supp_closed q. *)
(*   - apply/supp_closedP=> {}e1 {}e2. *)
(*     rewrite -eqsupp -eq_ica. *)
(*     by apply/supp_closedP. *)
(*   have eq_ica': (fs_ica p : hrel E E) \== fs_ica q. *)
(*   - by move=> ?? /=; rewrite eq_ica. *)
(*   apply/idP/idP. *)
(*   - move=> /(fs_caP _ _ supclp)/clos_rt_str. *)
(*     rewrite !(str_weq eq_ica')=> ?. *)
(*     by apply/(fs_caP _ _ supclq)/clos_rt_str. *)
(*   move=> /(fs_caP _ _ supclq)/clos_rt_str. *)
(*   rewrite -(str_weq eq_ica')=> ?. *)
(*   by apply/(fs_caP _ _ supclp)/clos_rt_str. *)
(* Qed. *)

(* End TheoryAux. *)

End Theory.

(* Section Empty. *)
(* Context (E : identType) (L : botType). *)
(* Implicit Types (p : lfspreposet E L). *)

(* Definition empty : lfspreposet E L := [fsfun]. *)

(* Lemma eventset_empty : *)
(*   lfsp_eventset empty = fset0. *)
(* Proof. by apply/fsetP=> e; rewrite !inE. Qed. *)

(* Lemma fs_size_empty : *)
(*   lfsp_size empty = 0%N. *)
(* Proof. by rewrite /lfsp_size eventset_empty. Qed. *)

(* Lemma fs_lab_empty : *)
(*   fs_lab empty =1 (fun=> bot). *)
(* Proof. by move=> ?; rewrite /fs_lab fsfun_dflt ?inE. Qed. *)

(* Lemma fs_ica_empty : *)
(*   fs_ica empty =2 (fun x y => false). *)
(* Proof. by move=> ??; rewrite /fs_ica /= /fs_rcov !fsfun_dflt ?inE. Qed. *)

(* Lemma fin_ica_empty : *)
(*   fin_ica empty =2 (fun x y => false). *)
(* Proof. by move=> *; rewrite -fin_ica_mono fs_ica_empty. Qed. *)

(* (* TODO: /start/ the following proofs should be simpler :( *) *)

(* Lemma fin_ca_empty : *)
(*   fin_ca empty =2 (fun x y => x == y). *)
(* Proof. *)
(*   move=> e1 e2; rewrite /fin_ca. *)
(*   apply/idP/idP; last first. *)
(*   - move=> /eqP ->; exact/connect_refl. *)
(*   move=> /connect_strP/clos_rt_str; elim=> //. *)
(*   - by move=> ??; rewrite fin_ica_empty. *)
(*   by move=> ???? /eqP-> ? /eqP->. *)
(* Qed. *)

(* Lemma fs_ca_empty : *)
(*   fs_ca empty =2 (fun x y => x == y). *)
(* Proof. *)
(*   move=> e1 e2; rewrite /fs_ca dhrel_qmkE /=. *)
(*   apply/orb_idr; rewrite /sub_rel_lift /=. *)
(*   case: insubP=> // e1' in1 <-. *)
(*   case: insubP=> // e2' in2 <-. *)
(*   by rewrite fin_ca_empty=> /eqP ->. *)
(* Qed. *)

(* (* TODO: /end/ the following proofs should be simpler :( *) *)

(* Lemma size0_empty p : *)
(*   supp_closed p -> lfsp_size p = 0%N -> p = empty. *)
(* Proof. *)
(*   move=> supcl. *)
(*   rewrite /lfsp_size=> /cardfs0_eq fE. *)
(*   apply/eqP/lfspreposet_eqP; split=> >. *)
(*   - rewrite fs_lab_empty fs_lab_bot ?fE //. *)
(*   rewrite fs_ica_empty /fs_ica /=. *)
(*   apply/idP; move/supp_closedP: supcl. *)
(*   by move=> /[apply]; rewrite fE => [[]]. *)
(* Qed. *)

(* Lemma empty_supp_closed : *)
(*   supp_closed empty. *)
(* Proof. by apply/supp_closedP=> ??; rewrite fs_ica_empty. Qed. *)

(* Lemma empty_acyclic : *)
(*   acyclic (fin_ica empty). *)
(* Proof. *)
(*   apply/acyclicP; split. *)
(*   - by move=> ?; rewrite /fin_ica /sub_rel_down /= fs_ica_empty. *)
(*   apply/forall2P=> e1 e2. *)
(*   apply/implyP=> /andP[]. *)
(*   have->: connect (fin_ica empty) e1 e2 = fin_ca empty e1 e2 by done. *)
(*   by rewrite fin_ca_empty=> /eqP->. *)
(* Qed. *)

(* Lemma empty_operational : *)
(*   operational empty. *)
(* Proof. *)
(*   apply/forall2P=> ??; rewrite fin_ca_empty. *)
(*   by apply/implyP=> /eqP->. *)
(* Qed. *)

(* Lemma empty_conseq_num : *)
(*   conseq_num empty. *)
(* Proof. *)
(*   rewrite /conseq_num eventset_empty. *)
(*   apply/eqP/fsetP=> e /=. *)
(*   rewrite in_fset /= inE in_nfresh encode0 addn0 /=. *)
(*   by rewrite fs_size_empty ltn0. *)
(* Qed. *)

(* Lemma empty_total : *)
(*   total (fin_ca empty). *)
(* Proof. *)
(*   case=> x xP; exfalso. *)
(*   by move: xP; rewrite eventset_empty. *)
(* Qed. *)

(* End Empty. *)

(* Arguments empty E L : clear implicits. *)

(* Section OfSeq. *)
(* Context (E : identType) (L : botType). *)
(* Implicit Types (p : lfspreposet E L). *)
(* Implicit Types (ls : seq L). *)

(* Definition of_seq ls :=  *)
(*   let fE  := [fset e | e in nfresh \i0 (size ls)] in  *)
(*   let lab := fun e : E => (nth bot ls (encode e)) in *)
(*   let ca  := fun e1 e2 : E => e1 <=^i e2 in *)
(*   @build_cov E L fE lab ca. *)

(* Variable (ls : seq L). *)
(* Hypothesis (lsD : bot \notin ls). *)

(* Lemma of_seq_nth_defined : *)
(*   forall (e : [fset e | e in nfresh \i0 (size ls)]), *)
(*     nth bot ls (@encode E (val e)) != bot. *)
(* Proof. *)
(*   move: lsD=> /negP nbl [/= ?]. *)
(*   rewrite ?inE /=; encodify; rewrite addn0=> ?. *)
(*   apply/negP; move: nbl=> /[swap]/eqP<-. *)
(*   by apply; apply/mem_nth. *)
(* Qed. *)

(* Lemma of_seq_eventset : *)
(*   lfsp_eventset (of_seq ls) = [fset e | e in nfresh \i0 (size ls)]. *)
(* Proof. rewrite build_eventset //; exact/of_seq_nth_defined. Qed. *)

(* (* TODO: derie from conseq_num *) *)
(* Lemma of_seq_fresh : *)
(*   lfsp_fresh (of_seq ls) = iter (size ls) fresh \i0. *)
(* Proof. *)
(*   rewrite /lfsp_fresh /fresh_seq of_seq_eventset. *)
(*   case: (boolP (size ls == 0%N))=> [|neq]. *)
(*   - rewrite size_eq0=> /eqP-> /=. *)
(*     by rewrite nfresh0 fset_nil /=. *)
(*   rewrite -fresh_seq_nfresh //. *)
(*   apply/max_set_eq; first exact/le0x. *)
(*   by apply/eq_mem_map=> x; rewrite !inE. *)
(* Qed. *)

(* Lemma of_seq_size : *)
(*   lfsp_size (of_seq ls) = size ls. *)
(* Proof. *)
(*   rewrite /lfsp_size of_seq_eventset card_fseq undup_id ?size_nfresh //. *)
(*   exact/lt_sorted_uniq/nfresh_sorted. *)
(* Qed. *)

(* Lemma of_seq_conseq_num : *)
(*   conseq_num (of_seq ls). *)
(* Proof. by rewrite /conseq_num of_seq_eventset of_seq_size. Qed. *)

(* Lemma of_seq_labE e : *)
(*   fs_lab (of_seq ls) e = nth bot ls (encode e). *)
(* Proof. *)
(*   rewrite /of_seq build_lab /= /sub_lift. *)
(*   case: insubP=> /= [?? ->|] //. *)
(*   rewrite ?inE /==> ?; rewrite nth_default; ilia. *)
(* Qed. *)

(* Lemma of_seq_fin_caE : *)
(*   fin_ca (of_seq ls) =2 relpre val [rel e1 e2 | e1 <=^i e2]. *)
(* Proof. *)
(*   apply/build_cov_fin_ca=> // [? ||]; last first. *)
(*   - exact/le_trans. *)
(*   - exact/le_anti. *)
(*   by rewrite of_seq_nth_defined. *)
(* Qed. *)

(* Lemma of_seq_fs_caE e1 e2 : *)
(*   fs_ca (of_seq ls) e1 e2 = *)
(*     (e1 == e2) || *)
(*     [&& e1 <=^i e2 *)
(*       , e1 \in lfsp_eventset (of_seq ls) *)
(*       & e2 \in lfsp_eventset (of_seq ls) *)
(*     ]. *)
(* Proof. *)
(*   rewrite of_seq_eventset /of_seq. *)
(*   rewrite build_cov_ca // => [? ||]; last first. *)
(*   - exact/le_trans. *)
(*   - exact/le_anti. *)
(*   by rewrite of_seq_nth_defined. *)
(* Qed. *)

(* Lemma of_seq_fin_icaE e1 e2 : *)
(*   fin_ica (of_seq ls) e1 e2 = (fresh (val e1) == val e2). *)
(* Proof. *)
(*   rewrite /of_seq build_cov_fin_ica; first last. *)
(*   - case=> /= ?; rewrite ?inE /==> ?. *)
(*     apply/eqP; move: lsD=> /[swap]<-. *)
(*     rewrite mem_nth=> //; ilia. *)
(*   apply/covP/eqP=> /=; case: e1 e2=> /= e1 i1 [/= e2 i2]. *)
(*   - case=> _ /andP[?? nex]. *)
(*     case: (fresh e1 =P e2)=> // /eqP ?; case: nex. *)
(*     move: i1 i2; rewrite of_seq_eventset ?inE /==> ??. *)
(*     have IN: (fresh e1 \in [fset e | e in nfresh \i0 (size ls)]). *)
(*     - rewrite ?inE /=; ilia. *)
(*     exists [`IN] => /=; rewrite /iker; ilia. *)
(*   split=> [/(congr1 val)||[[/= ? _]]]; rewrite /iker; ilia. *)
(* Qed. *)

(* Lemma of_seq_supp_closed : *)
(*   supp_closed (of_seq ls). *)
(* Proof. *)
(*   apply/supp_closedP=>>. *)
(*   rewrite build_ica build_eventset //; last first. *)
(*   - exact/of_seq_nth_defined. *)
(*   by move=> /sub_rel_liftP[[>[[>[? /= <- <-]]]]]. *)
(* Qed. *)

(* Hint Resolve of_seq_supp_closed : core. *)

(* Lemma of_seq_fs_icaE e1 e2 : *)
(*   fs_ica (of_seq ls) e1 e2 = *)
(*     [&& fresh e1 == e2 *)
(*       , e1 \in lfsp_eventset (of_seq ls) *)
(*       & e2 \in lfsp_eventset (of_seq ls) *)
(*     ]. *)
(* Proof. *)
(*   rewrite fs_ica_fin_icaE // /sub_rel_lift /=. *)
(*   case: insubP=> [? ->|/negbTE->]; last lattice. *)
(*   case: insubP=> [? ->|/negbTE-> //]; last by rewrite andbC. *)
(*   rewrite of_seq_fin_icaE=>->->; lattice. *)
(* Qed. *)

(* Lemma of_seq_acyclic : *)
(*   acyclic (fin_ica (of_seq ls)). *)
(* Proof. *)
(*   apply/build_cov_acyclic=> [? |||]; last first. *)
(*   - exact/le_trans. *)
(*   - exact/le_anti. *)
(*   - exact/le_refl. *)
(*   by rewrite of_seq_nth_defined. *)
(* Qed. *)

(* Lemma of_seq_operational : *)
(*   operational (of_seq ls). *)
(* Proof. *)
(*   apply/operationalP. *)
(*   move=> e1 e2; rewrite of_seq_fs_caE. *)
(*   by move=> /orP[/eqP->|/and3P[]]. *)
(* Qed. *)

(* Lemma of_seq_total : *)
(*   total (fin_ca (of_seq ls)). *)
(* Proof. move=> e1 e2; rewrite !of_seq_fin_caE /=; exact/le_total. Qed. *)

(* End OfSeq. *)

(* Arguments of_seq E L : clear implicits. *)

Section InterRel.
Context (E : identType) (L : botType).
Implicit Types (r : rel E).
Implicit Types (p : lfspreposet E L).

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
  @build_cov E L (lfsp_eventset p) (fs_lab p) (r \& (fs_ca p)).

(* Lemma inter_rel_finsupp r p :  *)
(*   lfsp_eventset (inter_rel r p) = lfsp_eventset p. *)
(* Proof. rewrite build_eventset //. apply/forallP. Qed. *)

Lemma inter_rel_labE r p :
  fs_lab (inter_rel r p) =1 fs_lab p.
Proof.
  move=> e; rewrite /inter_rel build_lab.
  case: (e \in lfsp_eventset p)/idP=> [eIn | enIn].
  - by rewrite sub_liftT.
  rewrite sub_liftF // fs_lab_bot //.
  exact/negP.
Qed.

Lemma inter_rel_supp_closed r p :
  supp_closed p -> supp_closed (inter_rel r p).
Proof.
  move=> supcl; apply/supp_closedP=>>.
  rewrite build_ica build_eventset //; last first.
  - by case=> e; rewrite /fin_lab /= inE /= => /andP[].
  by move=> /sub_rel_liftP[[>[[>[? /= <- <-]]]]].
Qed.

Variables (r : rel E) (p : lfspreposet E L).
Hypothesis (refl  : reflexive r).
Hypothesis (trans : transitive r).
Hypothesis (supcl : supp_closed p).
Hypothesis (acyc  : acyclic (fin_ica p)).

(* TODO: prove for lfposet? *)
Lemma inter_rel_acyclic :
  acyclic (fin_ica (inter_rel r p)).
Proof.
  apply/build_cov_acyclic.
  - by case=> e; rewrite /fin_lab /= inE /= => /andP[].
  - apply/refl_cap=> //; exact/fs_ca_refl.
  - under eq_antisym do rewrite capC.
    exact/antisym_cap/fs_ca_antisym.
  apply/trans_cap=> //; exact/fs_ca_trans.
Qed.

Lemma inter_rel_ca :
  fs_ca (inter_rel r p) =2 r \& (fs_ca p).
Proof.
  rewrite /inter_rel=> e1 e2.
  rewrite build_cov_ca_wf //.
  (* TODO: remove copy-paste! *)
  - by case=> e; rewrite /fin_lab /= inE /= => /andP[].
  - apply/refl_cap=> //; exact/fs_ca_refl.
  - under eq_antisym do rewrite capC.
    exact/antisym_cap/fs_ca_antisym.
  - apply/trans_cap=> //; exact/fs_ca_trans.
  move=> {}e1 {}e2 /andP[_] ca12.
  by apply/fs_ca_closed.
Qed.

End InterRel.

Section Restrict.
Context (E : identType) (L : botType).
Implicit Types (P : pred E).
Implicit Types (p : lfspreposet E L).

Definition restrict P p : lfspreposet E L :=
  (* TODO: there should be a simpler solution... *)
  let fE  := [fset e in lfsp_eventset p | P e] in
  let ca  := (eq_op \+ (P \x P)) \& (fs_ca p) in
  @build_cov E L fE (fs_lab p) ca.

Variables (P : pred E) (p : lfspreposet E L).
Hypothesis (supcl : supp_closed p).
Hypothesis (acyc  : acyclic (fin_ica p)).

Lemma restrict_finsupp :
  lfsp_eventset (restrict P p) = [fset e in lfsp_eventset p | P e].
Proof.
  apply/fsetP=> e; rewrite /restrict build_eventset //.
  by case=> e' /=; rewrite !inE -andbA => /and3P[].
Qed.

Lemma restrict_lab e :
  fs_lab (restrict P p) e = if P e then fs_lab p e else bot.
Proof.
  rewrite /restrict /build_cov build_lab /sub_lift /=.
  case: insubP; rewrite !inE=> //=.
  - by move=> ? /andP[? ->] ->.
  rewrite !negb_and negbK -(orbA)=> /or3P[].
  - move=> en; rewrite fs_lab_bot; first by case: ifP.
    by rewrite /lfsp_eventset inE /= negb_and en.
  - by move=> /eqP->; case: ifP.
  by move=> /negPf ->.
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
  - by case=> e /=; rewrite /lfsp_eventset !inE /= -andbA=> /and3P[].
  - apply/refl_cap=> //; last exact/fs_ca_refl.
    by move=> ? /=; rewrite eq_refl.
  - under eq_antisym do rewrite capC.
    exact/antisym_cap/fs_ca_antisym.
  - apply/trans_cap=> // [??? |] /=; last exact/fs_ca_trans.
    move=> /orP[/eqP->|/andP[??]] //.
    move=> /orP[/eqP<-|/andP[??]] //.
    1-2: by apply/orP; right; apply/andP.
  move=> /= {}e1 {}e2; rewrite /hrel_one /=.
  move=> /andP[/orP[->|/andP[p1 p2]]] //.
  move=> /(fs_ca_closed supcl acyc) /orP[->|] //.
  move=> /andP[]; rewrite /lfsp_eventset !inE=> /andP[??] /andP[??].
  by apply/orP; right; rewrite -?andbA; apply/and6P.
Qed.

Lemma restrict_acyclic :
  acyclic (fin_ica (restrict P p)).
Proof.
  apply/fin_ica_acyclic.
  - move=> x; rewrite /restrict build_cov_fin_ica; first exact/cov_irrefl.
    by case=> e /=; rewrite /lfsp_eventset !inE /= -andbA=> /and3P[].
  apply/fin_ca_antisym.
  move=> e1 e2 /= /andP[]; rewrite !restrict_ca //=.
  move=> /orP[/eqP->|] // + /orP[/eqP->|] //.
  move=> /and3P[???] /and3P[???].
  by apply/(fs_ca_antisym acyc)/andP.
Qed.

End Restrict.


Section Rename.
Context (E : identType) (L : botType).
Implicit Types (f : {fperm E}).
Implicit Types (p : lfspreposet E L).

Definition rename f p : lfspreposet E L :=
  let fE   := f @` (lfsp_eventset p) in
  let invF := (fperm_inv f) \o (val : fE -> E) in
  let lab  := (fs_lab p) \o invF in
  let ica  := [rel x y | fs_ica p (invF x) (invF y)] in
  build lab ica.

Lemma fperm_inv_inE f p e :
  (fperm_inv f e \in lfsp_eventset p) = (e \in f @` lfsp_eventset p).
Proof. rewrite -{2}[e](inv_fpermK f) mem_imfset //; exact/fperm_inj. Qed.

Lemma rename_lab f p : 
  fs_lab (rename f p) =1 (fs_lab p) \o (fperm_inv f).
Proof.
  move=> e; rewrite /rename build_lab //=.
  case: (e \in f @` (lfsp_eventset p))/idP=> [ein|enin].
  - by rewrite sub_liftT.
  rewrite sub_liftF ?fs_lab_bot ?fperm_inv_inE //; exact/negP.
Qed.

Lemma rename_eventset f p : 
  lfsp_eventset (rename f p) = f @` (lfsp_eventset p).
Proof.
  rewrite /rename build_eventset // => e.
  rewrite fs_labNbotE fperm_inv_inE; exact/valP.
Qed.

Lemma rename_ica f p : supp_closed p ->
  fs_ica (rename f p) =2 [rel x y | fs_ica p (fperm_inv f x) (fperm_inv f y)].
Proof.
  move=> supcl x y; rewrite /rename build_ica.
  case: (x \in f @` lfsp_eventset p)/idP; last first.
  - move=> /negP xnin; rewrite /sub_rel_lift /=. 
    rewrite insubF; last exact/(introF idP)/negP.
    symmetry; apply/(introF idP)/fs_ica_nsupp=> //.
    by apply/orP; left; rewrite fperm_inv_inE.
  case: (y \in f @` lfsp_eventset p)/idP; last first.
  - move=> /negP ynin xin; rewrite /sub_rel_lift /=. 
    rewrite insubT insubF; last exact/(introF idP)/negP.
    symmetry; apply/(introF idP)/fs_ica_nsupp=> //.
    by apply/orP; right; rewrite fperm_inv_inE.
  move=> iny inx. 
  have->: x = val [` inx] by done.
  have->: y = val [` iny] by done.
  by rewrite sub_rel_lift_val /=.
Qed.

Lemma rename_supp_closed f p : 
  supp_closed p -> supp_closed (rename f p).
Proof. 
  move=> supcl; apply/supp_closedP=> x y.
  rewrite rename_ica //=.
  move=> /(supp_closedP _ supcl)[].
  by rewrite !fperm_inv_inE rename_eventset.
Qed.

Lemma rename_ca f p : supp_closed p -> acyclic (fin_ica p) ->
  fs_ca (rename f p) =2 [rel x y | fs_ca p (fperm_inv f x) (fperm_inv f y)].
Proof.
  move=> supcl acyc x y; apply/eqP/iff_eqP; apply: iff_trans.
  - symmetry; apply: rwP; exact/fs_caP/rename_supp_closed.
  symmetry; apply: iff_trans; last split.
  - symmetry; apply: rwP=> /=; exact/fs_caP.
  - rewrite -{2}[x](inv_fpermK f) -{2}[y](inv_fpermK f).
    elim=> //=; last first.
    +  move=> {}x {}y {}z _ xy _ yz; exact/(rt_trans _ _ _ _ _ xy yz). 
    move=> {}x {}y icaxy; apply/rt_step.
    by rewrite rename_ica //= !fperm_invK.
  elim=> //=; last first.
  - move=> {}x {}y {}z _ xy _ yz; exact/(rt_trans _ _ _ _ _ xy yz). 
  move=> {}x {}y icaxy; apply/rt_step.
  by move: icaxy; rewrite rename_ica.
Qed.

Lemma rename_acyclic f p : supp_closed p -> acyclic (fin_ica p) ->
  acyclic (fin_ica (rename f p)).
Proof.
  move=> suplc acyc; apply/fin_ica_acyclic.
  - apply/fin_ica_irrefl.
    move=> e; rewrite rename_ica //.
    apply/fs_ica_irrefl=> //. 
    exact/acyc_irrefl.
  apply/fin_ca_antisym.
  move=> e1 e2; rewrite !rename_ca //=.
  move=> ?; apply/(@fperm_inv_inj _ f).
  exact/(fs_ca_antisym acyc). 
Qed.

End Rename.


Section Relabel.
Context (E : identType) (L1 : botType) (L2 : botType).
Implicit Types (f : L1 -> L2).
Implicit Types (p : lfspreposet E L1).

Definition relabel f p : lfspreposet E L2 :=
  [fsfun e in finsupp p => (f (fs_lab p e), fs_rcov p e)].

Variables (f : L1 -> L2) (p : lfspreposet E L1).
(* TODO: use inhtype to get rid of explicit bot arguments... *)
Hypothesis (fbot : {homo bot f}).
Hypothesis (fsupp : finsupp_preserving p f).

(* TODO: refactor this precondition? *)
(* Hypothesis (flabD : forall e, let l := fs_lab p e in (l == bot1) = (f l == bot2)). *)
(* Hypothesis (labD : lab_defined (relabel f p)). *)

Lemma relabel_lab :
  fs_lab (relabel f p) =1 (f \o fs_lab p).
Proof.
  rewrite /relabel /fs_lab=> e /=.
  rewrite fsfun_fun; case: ifP=> //=.
  move=> /negP nIn /=; apply/esym/eqP.
  rewrite fsfun_dflt ?fbot //=.
  exact/negP.
Qed.

Lemma relabel_eventset :
  lfsp_eventset (relabel f p) = lfsp_eventset p.
Proof.
  apply/fsetP=> e; rewrite /relabel.
  rewrite -?fs_labNbotE relabel_lab /=.
  case: (e \in lfsp_eventset p)/idP=> [|/negP]. 
  - move=> /[dup] ein; rewrite -fs_labNbotE=> ->.
    apply/idP; move: fsupp=> /forallP. 
    by move=> /(_ (Sub e ein)).
  rewrite -fs_labNbotE negbK=> /eqP ->.
  by move: fbot=> /eqP ->; rewrite !eqxx.
Qed.

Lemma relabel_ica :
  fs_ica (relabel f p) =2 fs_ica p.
Proof.
  rewrite /fs_ica /relabel=> e1 e2 /=.
  rewrite /fs_rcov fsfun_fun.
  case: ifP=> //= /negP ?.
  rewrite fsfun_dflt ?inE //; exact/negP.
Qed.

Lemma relabel_supp_closed :
  supp_closed p -> supp_closed (relabel f p).
Proof.
  move=> supcl; apply/supp_closedP=> e1 e2.
  rewrite relabel_eventset relabel_ica=> ica.
  by apply/supp_closedP.
Qed.

Lemma relabel_ca :
  supp_closed p -> fs_ca (relabel f p) =2 fs_ca p.
Proof.
  move=> supcl; apply/fs_ca_ica_eq.
  - exact/relabel_supp_closed.
  - by rewrite relabel_eventset.
  exact/relabel_ica.
Qed.

Lemma relabel_acyclic :
  supp_closed p -> acyclic (fin_ica p) -> acyclic (fin_ica (relabel f p)).
Proof.
  move=> suplc acyc; apply/fin_ica_acyclic.
  - apply/fin_ica_irrefl.
    move=> e; rewrite relabel_ica.
    apply/fs_ica_irrefl=> //.
    exact/acyc_irrefl.
  apply/fin_ca_antisym.
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
Context (E : identType) (L : botType).

Structure lfsposet : Type := mklFsPoset {
  lfsposet_val :> lfspreposet E L ;
  _ : let p := lfsposet_val in
      supp_closed p && acyclic (fin_ica p)
}.

Canonical lfsposet_subType := Eval hnf in [subType for lfsposet_val].

Implicit Types (p : lfsposet).

Lemma lfsp_supp_closed p : supp_closed p.
Proof. by move: (valP p)=> /andP[]. Qed.

Lemma lfsp_acyclic p : acyclic (fin_ica p).
Proof. by move: (valP p)=> /andP[]. Qed.

End Def.
End Def.

Arguments lfsposet E L : clear implicits.

Module Export Instances.
Section Instances.

Definition lfsposet_eqMixin E L :=
  Eval hnf in [eqMixin of (lfsposet E L) by <:].
Canonical lfinposet_eqType E L :=
  Eval hnf in EqType (lfsposet E L) (@lfsposet_eqMixin E L).

Definition lfsposet_choiceMixin E L :=
  Eval hnf in [choiceMixin of (lfsposet E L) by <:].
Canonical lfsposet_choiceType E L :=
  Eval hnf in ChoiceType (lfsposet E L) (@lfsposet_choiceMixin E L).

(* Definition lfsposet_countMixin E (L : countType) bot := *)
(*   Eval hnf in [countMixin of (@lfsposet E L bot) by <:]. *)
(* Canonical lfsposet_countType E (L : countType) bot := *)
(*   Eval hnf in CountType (lfsposet E L bot) (@lfsposet_countMixin E L bot). *)

(* Canonical subFinfun_subCountType E (L : countType) bot := *)
(*   Eval hnf in [subCountType of (lfsposet E L bot)]. *)

End Instances.
End Instances.

Section BuildCov.
Context (E : identType) (L : botType).
Context (fE : {fset E}).
Implicit Types (p : lfsposet E L).
Implicit Types (lab : fE -> L) (ica : rel fE) (ca : rel E).

Variables (lab : E -> L) (ca : rel E).
Hypothesis labD : forall (e : fE), lab (val e) != bot.
Hypothesis ca_refl  : reflexive ca.
Hypothesis ca_anti  : antisymmetric ca.
Hypothesis ca_trans : transitive ca.

Lemma build_covP : 
  let p := lFsPrePoset.build_cov fE lab ca in
  supp_closed p && acyclic (fin_ica p).
Proof.
  apply/andP; split=> //; last first.
  - exact/lFsPrePoset.build_cov_acyclic.
  apply/supp_closedP=>>.
  rewrite lFsPrePoset.build_ica lFsPrePoset.build_eventset //.
  rewrite /sub_rel_lift //=.
  by do 2 case: insubP=> //.
Qed.

Definition build_cov := mklFsPoset build_covP.

End BuildCov.


Section Empty.
Context (E : identType) (L : botType).
Implicit Types (p : lfspreposet E L).

(* TODO: rename? *)
Lemma emptyP :
  let p := @lFsPrePoset.empty E L in
  supp_closed p && acyclic (fin_ica p).
Proof.
  apply/andP; split.
  - exact/lFsPrePoset.empty_supp_closed.
  exact/lFsPrePoset.empty_acyclic.
Qed.

Definition empty : lfsposet E L :=
  mklFsPoset emptyP.

End Empty.

Arguments empty E L : clear implicits.

Section OfSeq.
Context (E : identType) (L : botType).
Implicit Types (p : lfspreposet E L).
Implicit Types (ls : seq L).

Lemma of_seqP ls : bot \notin ls ->
  let p := lFsPrePoset.of_seq E L ls in
  supp_closed p && acyclic (fin_ica p).
Proof.
  move=> labD; apply/andP; split.
  - exact/lFsPrePoset.of_seq_supp_closed.
  exact/lFsPrePoset.of_seq_acyclic.
Qed.

Definition of_seq ls : lfsposet E L :=
  if bot \notin ls =P true is ReflectT nbl then
    mklFsPoset (of_seqP nbl)
  else empty E L.

Lemma of_seq_valE ls :
  val (of_seq ls) =
    if (bot \notin ls) then
      lFsPrePoset.of_seq E L ls
    else
      lFsPrePoset.empty E L.
Proof. by case: ifP; rewrite /of_seq; case: eqP=> //= ->. Qed.

Lemma of_seq_size ls :
  lfsp_size (of_seq ls) = if (bot \notin ls) then size ls else 0%N.
Proof.
  rewrite of_seq_valE; case: ifP=> ?.
  - by rewrite lFsPrePoset.of_seq_size.
  by rewrite lFsPrePoset.fs_size_empty.
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
      , e1 \in lfsp_eventset (of_seq ls)
      , e2 \in lfsp_eventset (of_seq ls)
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
Context (E : identType) (L : botType).
Context (p : lfsposet E L) (x : E).

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
Hypothesis x_max : [forall y : lfsp_eventset p, ~~ fs_ica p x (val y)].

(* TODO: move to lFsPoset.Theory *)
Lemma x_maximal : forall y, ~ fs_ica p x y.
Proof.
  move=> ? /[dup] /(supp_closedP _ (lfsp_supp_closed _))[_ i].
  by move/forallP/(_ [`i])/negP: x_max.
Qed.

Lemma delete_fs_lab :
  fs_lab delete_pre =1 fun e => if e == x then bot else fs_lab p e.
Proof. move=>>; rewrite /fs_lab fsfun_withE; by case: ifP. Qed.

Lemma delete_eventset :
  lfsp_eventset delete_pre = lfsp_eventset p `\ x.
Proof.
  rewrite /lfsp_eventset finsupp_without //.
  apply/fsetP=> e; rewrite !inE delete_fs_lab /=.
  by case: (e == x).
Qed.

Lemma delete_fs_ica :
  fs_ica delete_pre =2 [rel e1 e2 | if e2 != x then fs_ica p e1 e2 else false].
Proof. move=>>; rewrite /fs_ica /= /fs_rcov fsfun_withE; by case: ifP. Qed.

Lemma delete_supp_closed :
  supp_closed delete_pre.
Proof.
  apply/supp_closedP=> e1 e2.
  rewrite delete_fs_ica delete_eventset /=; case: ifP=> //=.
  rewrite !in_fsetD1=> -> /=; case: (e1 == x)/idP=> [|_] //=.
  - by move=> /eqP-> /x_maximal.
  by move/supp_closedP/(_ e1 e2): (lfsp_supp_closed p); apply.
Qed.

Lemma delete_fs_ca :
  fs_ca delete_pre =2 [rel e1 e2 | if e2 != x then fs_ca p e1 e2 else e1 == e2].
Proof.
  move=>>; apply/(fs_caP _ _ delete_supp_closed)/idP=> /=.
  - move/clos_rt_rtn1_iff; elim=> [|y ? + _] /=.
    + case: (_ =P _)=> //= _; exact/fs_ca_refl.
    rewrite delete_fs_ica /=; case: ifP=> //= ? ica_yz yx.
    apply/(fs_caP _ _ (lfsp_supp_closed p))/rt_trans; last first.
    + apply/clos_rt_rt1n_iff/clos_rt1n_step; exact/ica_yz.
    move: yx; case: ifP=> [|_ /eqP->]; last exact/rt_refl.
    by move=> ? /(fs_caP _ _ (lfsp_supp_closed p)).
  case: (_ =P _)=> /= [->/eqP->|/[swap]]; first by constructor.
  move/(fs_caP _ _ (lfsp_supp_closed p))/clos_rt_rtn1_iff.
  rewrite clos_rt_rtn1_iff.
  elim=> [|y ? + _]; first by constructor.
  case: (y =P x)=> [->/x_maximal //| nyx ? /(_ nyx) fi ?].
  econstructor; last exact/fi.
  rewrite delete_fs_ica /=; by case (_ =P _).
Qed.

Lemma delete_acyclic :
  acyclic (fin_ica delete_pre).
Proof.
  apply/fin_ica_acyclic.
  - apply/fin_ica_irrefl=> ?.
    rewrite delete_fs_ica /=; case: ifP=> // *.
    exact/fs_ica_irrefl/acyc_irrefl/lfsp_acyclic/lfsp_supp_closed.
  apply/fin_ca_antisym=> ??.
  rewrite? delete_fs_ca /=; case: ifP=> [_|_ /andP[/eqP->]] //.
  case: ifP=> [_|_ /andP[? /eqP->]] //.
  exact/fs_ca_antisym/lfsp_acyclic.
Qed.

Lemma deleteP :
  supp_closed delete_pre && acyclic (fin_ica delete_pre).
Proof. by rewrite delete_supp_closed delete_acyclic. Qed.

End DeletePre.

Definition delete :=
  if eqP is ReflectT pf then mklFsPoset (deleteP pf) else lFsPoset.empty E L.

Definition lfsp_delE:
  [forall y : lfsp_eventset p, ~~ fs_ica p x (val y)] ->
  (lfsp_eventset delete = lfsp_eventset p `\ x) *
  (fs_lab delete =1 fun e => if e == x then bot else fs_lab p e) *
  (fs_ica delete =2 [rel e1 e2 | if e2 != x then fs_ica p e1 e2 else false]) *
  (fs_ca delete  =2 [rel e1 e2 | if e2 != x then fs_ca p e1 e2 else e1 == e2]).
Proof.
  by move=> *; rewrite /delete; case: eqP=> //=; do ? split=>>;
    rewrite (delete_eventset, delete_fs_ca, delete_fs_ica, delete_fs_lab).
Qed.

End DeleteMax.

Arguments of_seq E L : clear implicits.

Section InterRel.
Context (E : identType) (L : botType).
Implicit Types (p : lfsposet E L).

Variable (r : rel E).
Hypothesis (refl  : reflexive r).
Hypothesis (trans : transitive r).

Lemma inter_relP p :
  let q := lFsPrePoset.inter_rel r p in
  supp_closed q && acyclic (fin_ica q).
Proof.
  move: (lfsp_supp_closed p)=> supcl.
  move: (lfsp_acyclic p)=> acyc.
  apply/andP; split.
  - exact/lFsPrePoset.inter_rel_supp_closed.
  exact/lFsPrePoset.inter_rel_acyclic.
Qed.

Definition inter_rel p := mklFsPoset (inter_relP p).

End InterRel.

Arguments inter_rel {E L} r.

Section Inter.
Context (E : identType) (L : botType).
Implicit Types (p q : lfsposet E L).

Definition inter p q :=
  inter_rel (fs_ca p) (fs_ca_refl p) (@fs_ca_trans _ _ p) q.

End Inter.

Section Restrict.
Context (E : identType) (L : botType).
Implicit Types (P : pred E).
Implicit Types (p : lfsposet E L).

Lemma restrictP P p :
  let q := lFsPrePoset.restrict P p in
  supp_closed q && acyclic (fin_ica q).
Proof.
  move: (lfsp_supp_closed p)=> supcl.
  move: (lfsp_acyclic p)=> acyc.
  apply/andP; split.
  - exact/lFsPrePoset.restrict_supp_closed.
  exact/lFsPrePoset.restrict_acyclic.
Qed.

Definition restrict P p := mklFsPoset (restrictP P p).

Lemma restrict_valE P p :
  val (restrict P p) = lFsPrePoset.restrict P p.
Proof. done. Qed.

End Restrict.

Section Rename.
Context (E : identType) (L : botType).
Implicit Types (f : {fperm E}).
Implicit Types (p : lfsposet E L).

Lemma renameP f p : 
  let q := lFsPrePoset.rename f p in
  supp_closed q && acyclic (fin_ica q).
Proof.
  move: (lfsp_supp_closed p)=> supcl.
  move: (lfsp_acyclic p)=> acyc.
  apply/andP; split.
  - exact/lFsPrePoset.rename_supp_closed. 
  exact/lFsPrePoset.rename_acyclic. 
Qed.

Definition rename f p := mklFsPoset (renameP f p).

(* Variable (f : {fperm E}) (p : lfsposet E L). *)

(* Lemma relabel_valE :  *)
(*   val (rename f p) = lFsPrePoset.rename f p. *)
(* Proof. done. Qed. *)

End Rename.

Section Relabel.
Context (E : identType) (L1 : botType) (L2 : botType).
Implicit Types (f : L1 -> L2).
Implicit Types (p : lfsposet E L1).

(* Hypothesis (flabD : forall e, let l := fs_lab p e in (l == bot1) = (f l == bot2)). *)
(* Hypothesis (flabD : forall l, (l == bot1) = (f l == bot2)). *)
(* Hypothesis (labD : lab_defined p). *)

Lemma relabelP f p :
  {homo bot f} -> finsupp_preserving p f ->
  let q := @lFsPrePoset.relabel E L1 L2 f p in
  supp_closed q && acyclic (fin_ica q).
Proof.
  move=> fbot fsupp.
  move: (lfsp_supp_closed p)=> supcl.
  move: (lfsp_acyclic p)=> acyc.
  apply/andP; split.
  - exact/lFsPrePoset.relabel_supp_closed.
  exact/lFsPrePoset.relabel_acyclic.
Qed.

Definition relabel f p :=
  match {homo bot f} && (finsupp_preserving p f) =P true with
  | ReflectF _  => lFsPoset.empty E L2
  | ReflectT pf =>
    let: conj fbot fsupp := andP pf in
    mklFsPoset (relabelP fbot fsupp)
  end.

Variable (f : L1 -> L2) (p : lfsposet E L1).
Hypothesis (fbot : {homo bot f}).
Hypothesis (fsupp : finsupp_preserving p f).

Lemma relabel_valE :
  val (relabel f p) = @lFsPrePoset.relabel E L1 L2 f p.
Proof.
  rewrite /relabel; case: eqP=> [pf|] //=.
  - by case: (andP pf).
  by move=> /negP; rewrite negb_and=> /orP[|] /negP.
Qed.

End Relabel.

Arguments relabel {E L1 L2} f p.

Module Export POrder.
Section POrder.
Context {E : identType} {L : botType}.
Variable (bot : L) (p : lfsposet E L).

Definition lfsposet_porderMixin :=
  @LePOrderMixin E (fs_ca p) (fs_sca p)
    (scaE p)
    (fs_ca_refl p)
    (fs_ca_antisym (lfsp_acyclic p))
    (@fs_ca_trans _ _ p).

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
Context (E : identType) (L : botType).
Variable (p : lfsposet E L).

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
Context {E : identType} {L : botType}.
Implicit Types (p q : lfsposet E L).

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
Proof. by move=> x y; rewrite fin_caE fs_caE fin_ca_mono. Qed.

End Theory.
End Theory.

Import lPoset.Syntax.

Module Export Hom.
Section Hom.
Context {E1 E2 : identType} {L : botType}.
Implicit Types (p : lfsposet E1 L) (q : lfsposet E2 L).
Implicit Types (f : E1 -> E2).

Definition is_hom f p q :=
  let f : [Event of p] -> [Event of q] := f in
  [/\                          {mono f : e / lab e}
    & {in (lfsp_eventset p) &, {homo f : e1 e2 / e1 <= e2}}
  ].

Variables (p : lfsposet E1 L) (q : lfsposet E2 L).
Variables (f : E1 -> E2) (ff : {ffun [FinEvent of p] -> [FinEvent of q]}).
Hypothesis (feq : forall e : lfsp_eventset p, f (val e) = val (ff e)).

Lemma mono_labW :
  let f : [Event of p] -> [Event of q] := f in
  {mono f : e / lab e} -> [forall e, lab (ff e) == lab e].
Proof.
  move=> /= flab; apply/mono1P=> x.
  rewrite ?fin_labE -?fin_lab_mono -?feq; exact/flab.
Qed.

Lemma homo_caP :
  let f : [Event of p] -> [Event of q] := f in
  reflect {in (lfsp_eventset p) &, {homo f : e1 e2 / e1 <= e2}}
          [forall e1, forall e2, (e1 <= e2) ==> (ff e1 <= ff e2)].
Proof.
  apply/(equivP (homo2P _ _ _)); split=> fhom x y; last first.
  - rewrite ?fin_caE -?fin_ca_mono -?feq.
    move=> le_xy; apply/fhom=> //; exact/valP.
  move=> xin yin le_xy.
  have->: x = val (Sub x xin : lfsp_eventset p)=> //.
  have->: y = val (Sub y yin : lfsp_eventset p)=> //.
  rewrite !feq fs_caE fin_ca_mono; apply/fhom.
  by rewrite fin_caE -fin_ca_mono.
Qed.

Lemma mono_caP :
  let f : [Event of p] -> [Event of q] := f in
  reflect {in (lfsp_eventset p) &, {mono f : e1 e2 / e1 <= e2}}
          [forall e1, forall e2, (ff e1 <= ff e2) == (e1 <= e2)].
Proof.
  apply/(equivP (mono2P _ _ _)); split=> fmon x y; last first.
  - rewrite ?fin_caE -?fin_ca_mono -?feq -?fs_caE fmon //; exact/valP.
  move=> xin yin.
  have->: x = val (Sub x xin : lfsp_eventset p)=> //.
  have->: y = val (Sub y yin : lfsp_eventset p)=> //.
  by rewrite ?feq ?fs_caE ?fin_ca_mono -?fin_caE fmon.
Qed.

Lemma is_hom_fin :
  is_hom f p q -> lFinPoset.Hom.axiom ff.
Proof. move=> [??]; apply/andP; split; [exact/mono_labW | exact/homo_caP]. Qed.

Hypothesis (fsup : forall e, e \notin lfsp_eventset p -> f e \notin lfsp_eventset q).

Lemma mono_labS :
  let f : [Event of p] -> [Event of q] := f in
  [forall e, lab (ff e) == lab e] -> {mono f : e / lab e}.
Proof.
  move=> /= /mono1P flab x.
  case: (x \in lfsp_eventset p)/idP=> [xin|xnin].
  - have->: x = val (Sub x xin : lfsp_eventset p)=> //.
    rewrite feq !fs_labE !fin_lab_mono; exact/flab.
  rewrite !fs_labE !fs_lab_bot //; [|apply/fsup]; exact/negP.
Qed.

(* TODO: move this lemma to appropriate place *)
Lemma mono_lab_eventset e :
  let f : [Event of p] -> [Event of q] := f in
  {mono f : e / lab e} -> (e \in lfsp_eventset p) = (f e \in lfsp_eventset q). 
Proof. by move=> /= labf; rewrite -?fs_labNbotE -?fs_labE labf. Qed.

Lemma fin_is_hom :
  lFinPoset.Hom.axiom ff -> is_hom f p q.
Proof. move=> /andP[??]; split; [exact/mono_labS | exact/homo_caP]. Qed.

Definition hom_lift : E1 -> E2 :=
  sub_lift (fun=> fresh_seq (lfsp_eventset q)) (fun e => val (ff e)).

Lemma hom_lift_eq (e : lfsp_eventset p) :
  hom_lift (val e) = val (ff e).
Proof.
  rewrite /hom_lift sub_liftT //=.
  by move=> ein; rewrite sub_val.
Qed.

Lemma hom_lift_Nfinsupp e :
  e \notin lfsp_eventset p -> hom_lift e \notin lfsp_eventset q.
Proof.
  move=> /negP en; rewrite /hom_lift sub_liftF //.
  exact/fresh_seq_nmem.
Qed.

Hypothesis (homf : is_hom f p q).

Lemma is_hom_eventset e :
  e \in lfsp_eventset p -> (f e) \in lfsp_eventset q.
Proof. by rewrite mono_lab_eventset; case homf. Qed.

Definition hom_down : {ffun [FinEvent of p] -> [FinEvent of q]} :=
  [ffun e => [` is_hom_eventset (valP e)] ].

Lemma hom_down_eq (e : lfsp_eventset p) :
  f (val e) = val (hom_down e).
Proof. by rewrite ffunE. Qed.

End Hom.

Arguments is_hom {_ _ _} _ _.

Section hPreOrder.
Context {E1 E2 : identType} {L : botType}.
Implicit Types (p : lfsposet E1 L) (q : lfsposet E2 L).

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
  is_hom f p q -> (e \in lfsp_eventset p) = (f e \in lfsp_eventset q).
Proof. move=> [] fmon ?; by rewrite -?fs_labNbotE -?fs_labE fmon. Qed.

End hPreOrder.

Section PreOrder.
Context {E : identType} {L : botType}.
Implicit Types (p q : lfsposet E L).

(* TODO: this relation should also be heterogeneous? *)
Definition hom_lt : rel (lfsposet E L) :=
  fun p q => (q != p) && (hom_le p q).

Lemma hom_lt_def p q : hom_lt p q = (q != p) && (hom_le p q).
Proof. done. Qed.

Lemma hom_le_refl : reflexive (@hom_le E E L).
Proof. move=> ?; exact/lFinPoset.Hom.hom_le_refl. Qed.

Lemma hom_le_trans : transitive (@hom_le E E L).
Proof. move=> ??? /[swap]; exact/lFinPoset.Hom.hom_le_trans. Qed.

Lemma is_hom_id_finsuppE p q :
  is_hom id p q -> lfsp_eventset p = lfsp_eventset q.
Proof. by move=> hf; apply/fsetP=> e; rewrite (is_hom_in_finsuppE _ hf). Qed.

Lemma is_hom_operational p q :
  is_hom id p q -> operational q -> operational p.
Proof.
  (do ? case)=> _ cm /operationalP sb.
  apply/forall2P=> /= x y.
  apply/implyP; rewrite -fin_ca_mono=> /cm /sb.
  apply; exact/valP.
Qed.

End PreOrder.

End Hom.

Module Export iHom.
Section iHom.
Context {E1 E2 : identType} {L : botType}.
Implicit Types (p : lfsposet E1 L) (q : lfsposet E2 L).
Implicit Types (f : E1 -> E2).

Definition is_ihom f p q :=
  let f : [Event of p] -> [Event of q] := f in
  [/\                          {mono f : e / lab e}
    , {in (lfsp_eventset p) &, {homo f : e1 e2 / e1 <= e2}}
    & {in (lfsp_eventset p) &, injective f}
  ].

Variables (p : lfsposet E1 L) (q : lfsposet E2 L).
Variables (f : E1 -> E2) (ff : {ffun [FinEvent of p] -> [FinEvent of q]}).
Hypothesis (feq : forall e : lfsp_eventset p, f (val e) = val (ff e)).

Lemma injective_onP :
  reflect {in (lfsp_eventset p) &, injective f} (injectiveb ff).
Proof.
  apply/(equivP (injectiveP _)); split=> injf; last first.
  - move=> x y efxy; apply/val_inj/injf; try exact/valP.
    by rewrite ?feq efxy.
  move=> /= x y xin yin exy.
  have->: x = val (Sub x xin : lfsp_eventset p)=> //.
  have->: y = val (Sub y yin : lfsp_eventset p)=> //.
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

Hypothesis (fsup : forall e, e \notin lfsp_eventset p -> f e \notin lfsp_eventset q).

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

Arguments is_ihom {_ _ _} _ _.

Section hPreOrder.
Context {E1 E2 : identType} {L : botType}.
Implicit Types (p : lfsposet E1 L) (q : lfsposet E2 L).

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
  ihom_le p q -> lfsp_size q <= lfsp_size p.
Proof.
  rewrite /ihom_le /lfsp_size ?cardfE=> /lFinPoset.iHom.ihom_leP[/=] f.
  exact/leq_card/(@ihom_inj _ _ _ f).
Qed.

End hPreOrder.

Section PreOrder.
Context (E : identType) (L : botType).
Implicit Types (p q : lfsposet E L).

(* TODO: this relation should also be heterogeneous? *)
Definition ihom_lt : rel (lfsposet E L) :=
  fun p q => (q != p) && (ihom_le p q).

Lemma ihom_lt_def p q : ihom_lt p q = (q != p) && (ihom_le p q).
Proof. done. Qed.

Lemma ihom_le_refl : reflexive (@ihom_le E E L).
Proof. move=> ?; exact/lFinPoset.iHom.ihom_le_refl. Qed.

Lemma ihom_le_trans : transitive (@ihom_le E E L).
Proof. move=> ??? /[swap]; exact/lFinPoset.iHom.ihom_le_trans. Qed.

End PreOrder.

End iHom.


Module Export bHom.
Section bHom.
Context {E1 E2 : identType} {L : botType}.
Implicit Types (p : lfsposet E1 L) (q : lfsposet E2 L).
Implicit Types (f : E1 -> E2).

Definition is_bhom f p q :=
  let f : [Event of p] -> [Event of q] := f in
  [/\                          {mono f : e / lab e}
    , {in (lfsp_eventset p) &, {homo f : e1 e2 / e1 <= e2}}
    & {on (lfsp_eventset q)  , bijective f}
  ].

Variables (p : lfsposet E1 L) (q : lfsposet E2 L).
Variables (f : E1 -> E2) (ff : {ffun [FinEvent of p] -> [FinEvent of q]}).
Hypothesis (feq : forall e : lfsp_eventset p, f (val e) = val (ff e)).

Lemma bijective_onW :
  let f : [Event of p] -> [Event of q] := f in
  {mono f : e / lab e} -> {on (lfsp_eventset q), bijective f} -> bijectiveb ff.
Proof.
  move=> /= labf; case=> g K K'; apply/bijectiveP.
  have suppg : forall e, e \in lfsp_eventset q -> (g e) \in lfsp_eventset p.
  - move=> x /[dup] xin; rewrite -fs_labNbotE -fs_labNbotE -fs_labE -fs_labE. 
    by rewrite -?labf; apply/contra; rewrite K'. 
  pose gg : [FinEvent of q] -> [FinEvent of p] := 
    fun e => Sub (g (val e)) (suppg (val e) (valP e)). 
  exists gg=> e; rewrite /gg; apply/val_inj=> /=; rewrite -?feq /= ?K ?K' //. 
  rewrite -(Hom.mono_lab_eventset _ labf); exact/valP.
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

Hypothesis (fsup : forall e, e \notin lfsp_eventset p -> f e \notin lfsp_eventset q).

Lemma bijective_onS :
  let f : [Event of p] -> [Event of q] := f in
  {mono f : e / lab e} -> bijectiveb ff -> {on (lfsp_eventset q), bijective f}.
Proof.
  move=> /= labf /bijectiveP[] gg K K'.
  pose g := Hom.hom_lift (finfun gg).
  have geq: forall e, g (val e) = val (gg e).
  - move=> /= e; rewrite /g /Hom.hom_lift sub_liftT // => ein.
    congr val; rewrite ffunE; congr gg; exact/sub_val.
  exists g=> [x | x xin]; last first.
  - have->: x = val (Sub x xin : [FinEvent of q]) by done.
    by rewrite geq feq K'.
  move=> /[dup] fxin; rewrite -(Hom.mono_lab_eventset _ labf)=> xin.
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

Arguments is_bhom {_ _ _} _ _.

Section hPreOrder.
Context {E1 E2 : identType} {L : botType}.
Implicit Types (p : lfsposet E1 L) (q : lfsposet E2 L).

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
  bhom_le p q -> lfsp_size p = lfsp_size q.
Proof.
  rewrite /bhom_le /lfsp_size ?cardfE=> /lFinPoset.bHom.bhom_leP [/=] f.
  by move: (bij_eq_card (bhom_bij f)).
Qed.

End hPreOrder.

Section PreOrder.
Context (E : identType) (L : botType).
Implicit Types (p q : lfsposet E L).

(* TODO: this relation should also be heterogeneous? *)
Definition bhom_lt : rel (lfsposet E L) :=
  fun p q => (q != p) && (bhom_le p q).

Definition lin E L (p : lfsposet E L) : pred (seq L) :=
  [pred ls | bhom_le (lFsPoset.of_seq E L ls) p].

Lemma bhom_lt_def p q : bhom_lt p q = (q != p) && (bhom_le p q).
Proof. done. Qed.

Lemma bhom_le_refl : reflexive (@bhom_le E E L).
Proof. move=> ?; exact/lFinPoset.bHom.bhom_le_refl. Qed.

Lemma bhom_le_trans : transitive (@bhom_le E E L).
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
Context {E1 E2 : identType} {L : botType}.
Implicit Types (p : lfsposet E1 L) (q : lfsposet E2 L).
Implicit Types (f : E1 -> E2).

Definition is_emb f p q :=
  let f : [Event of p] -> [Event of q] := f in
  [/\                          {mono f : e / lab e}
    & {in (lfsp_eventset p) &, {mono f : e1 e2 / e1 <= e2}}
  ].

Variables (p : lfsposet E1 L) (q : lfsposet E2 L).
Variables (f : E1 -> E2) (ff : {ffun [FinEvent of p] -> [FinEvent of q]}).
Hypothesis (feq : forall e : lfsp_eventset p, f (val e) = val (ff e)).

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

Hypothesis (fsup : forall e, e \notin lfsp_eventset p -> f e \notin lfsp_eventset q).

Lemma fin_is_emb :
  lFinPoset.Emb.axiom ff -> is_emb f p q.
Proof.
  move=> /andP[???]; split;
    [ exact/Hom.mono_labS
    | exact/Hom.mono_caP
    ].
Qed.

End Emb.

Arguments is_emb {_ _ _} _ _.

Section hPreOrder.
Context {E1 E2 : identType} {L : botType}.
Implicit Types (p : lfsposet E1 L) (q : lfsposet E2 L).

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
  emb_le p q -> lfsp_size q <= lfsp_size p.
Proof. by move=> /emb_ihom_le /ihom_le_size. Qed.

Lemma emb_fs_ca f p q (X : {fset E1}) : is_emb f p q -> {in X &, injective f} ->
  let f : [Event of p] -> [Event of q] := f in
  {in X &, {mono f : e1 e2 / e1 <= e2}}.
Proof.
  move=> [] labf monf injf /= e1 e2 in1 in2 /=; apply/esym.
  case: ((e1 \notin lfsp_eventset p) || (e2 \notin lfsp_eventset p))/idP=> [ns|].
  - apply/idP/idP=> /(fs_ca_nsupp (lfsp_supp_closed _) (lfsp_acyclic _)).
    + move=> /(_ ns) /=-> //; exact/fs_ca_refl.
    rewrite -?(Hom.mono_lab_eventset _ labf) ns.
    move=> /(_ erefl)/(injf _ _ in1 in2)->.
    exact/fs_ca_refl.
  move/negP; rewrite negb_or ?negbK=> /andP[*].
  by rewrite -?fs_caE monf.
Qed.

Lemma emb_dw_clos f p q es e :
  is_emb f p q -> es `<=` lfsp_eventset p -> f @` es `<=` lfsp_eventset q ->
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
    + move: ca=> /(fs_ca_closed psupcl pacyc) /orP[/eqP->|/andP[]] //.
    by apply/imfsetP; exists e'.
  case/imfsetP=> /= {}e' /[swap]->.
  move=> /[dup] ? /(fsubsetP subs) ein ca; exists e'=> //.
  rewrite -fs_caE -monf //.
  move: ca=> /(fs_ca_closed qsupcl qacyc).
  rewrite -?(Hom.mono_lab_eventset _ labf).
  move=> /orP[/eqP|/andP[]] //.
  rewrite (Hom.mono_lab_eventset _ labf)=> ->.
  by rewrite -(Hom.mono_lab_eventset _ labf).
Qed.

End hPreOrder.

Section PreOrder.
Context (E : identType) (L : botType).
Implicit Types (p q : lfsposet E L).

(* TODO: this relation should also be heterogeneous? *)
Definition emb_lt : rel (lfsposet E L) :=
  fun p q => (q != p) && (emb_le p q).

Lemma emb_lt_def p q : emb_lt p q = (q != p) && (emb_le p q).
Proof. done. Qed.

Lemma emb_le_refl : reflexive (@emb_le E E L).
Proof. move=> ?; exact/lFinPoset.Emb.emb_le_refl. Qed.

Lemma emb_le_trans : transitive (@emb_le E E L).
Proof. move=> ??? /[swap]; exact/lFinPoset.Emb.emb_le_trans. Qed.

End PreOrder.

End Emb.


Module Export Iso.
Section Iso.
Context {E1 E2 : identType} {L : botType}.
Implicit Types (p : lfsposet E1 L) (q : lfsposet E2 L).
Implicit Types (f : E1 -> E2).

Definition is_iso f p q :=
  let f : [Event of p] -> [Event of q] := f in
  [/\                          {mono f : e / lab e}
    , {in (lfsp_eventset p) &, {mono f : e1 e2 / e1 <= e2}}
    & {on (lfsp_eventset q)  , bijective f}
  ].

Variables (p : lfsposet E1 L) (q : lfsposet E2 L).
Variables (f : E1 -> E2) (ff : {ffun [FinEvent of p] -> [FinEvent of q]}).
Hypothesis (feq : forall e : lfsp_eventset p, f (val e) = val (ff e)).

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

Hypothesis (fsup : forall e, e \notin lfsp_eventset p -> f e \notin lfsp_eventset q).

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
Context {E1 E2 : identType} {L : botType}.
Implicit Types (p : lfsposet E1 L) (q : lfsposet E2 L).

Definition iso_eqv p q :=
  let EP := [FinEvent of p] in
  let EQ := [FinEvent of q] in
  ??|{ffun EQ -> EP | lFinPoset.Iso.axiom}|.

Lemma iso_eqvP p q :
  reflect (exists (f : E2 -> E1), is_iso f q p) (iso_eqv p q).
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
  iso_eqv p q -> lfsp_size p = lfsp_size q.
Proof. by move=> /iso_bhom_le /bhom_le_size. Qed.

Lemma bhom_factor p q : bhom_le p q ->
  exists2 q' : lfsposet E1 L, iso_eqv q' q & is_hom id q' p.
Proof.
  case/bhom_leP=> f [labf homf [/= g K K']].
  set fE := lfsp_eventset p.
  set fl : E1 -> L := fun e => lab (g e : [Event of q]).
  set ca  : rel E1  := fun e1 e2 => 
    (e1 == e2) || 
    [&& fs_ca q (g e1) (g e2), e1 \in lfsp_eventset p & e2 \in lfsp_eventset p].
  have [: a1 a2 a3 a4] @q' :=
    @lFsPoset.build_cov E1 L fE fl ca a1 a2 a3 a4.
  - by case=> e ein; rewrite /= /fl -labf K' //= fs_labE fs_labNbotE. 
  - by move=> ?; rewrite /ca eqxx.
  - move=> e1 e2 /andP[] /orP[/eqP-> //|/and3P[+ e1In e2In]].
    move=> /homf; rewrite !(Hom.mono_lab_eventset _ labf) ?K' //.
    move=>/(_ e1In e2In)/[swap].
    case/orP=>[/eqP->//|/and3P[+??]].
    move=> /homf; rewrite !(Hom.mono_lab_eventset _ labf) ?K' //.
    move=>/(_ e2In e1In)/[swap].
    move=> ??; suff: e1 = e2 :> [Event of p] by done.
    exact/le_anti/andP.
  - set ft := (@fs_ca_trans _ _ q).
    move=>>; rewrite /ca => /orP[/eqP->//|/and3P[/[dup] fc /ft tr i1 i2]].
    move/orP=>[/eqP<-|]; rewrite ?fc ?i1 i2 //=.
    by move/andP=> [/tr->]->.
  exists q'; first (apply/iso_eqvP=> /=; exists f); repeat split.
  - move=> x; rewrite ?fs_labE ?/(_ <= _) /=.
    rewrite lFsPrePoset.build_lab /sub_lift.
    case: insubP=> /=; rewrite /fl.
    + by case=> /= ???->; rewrite K.
    by rewrite -fs_labNbotE -?fs_labE labf eq_sym negbK=> /eqP. 
  - move=> e1 e2 e1In e2In; rewrite ?/(_ <= _) /=.
    rewrite lFsPrePoset.build_cov_ca_wf ?/ca //; last first.
    + move=> x y /orP[/eqP->|/and3P[]] //=; rewrite ?/hrel_one ?eqxx //.
      by rewrite /fE=> ? -> ->.
    rewrite ?K -?(Hom.mono_lab_eventset _ labf) //.
    rewrite e1In e2In !andbT; apply: orb_idl=> /eqP.
    suff: {on lfsp_eventset p &, injective f}.
    - move=> /[apply]; rewrite -?(Hom.mono_lab_eventset _ labf) //.
      move=> /(_ e1In e2In) ->; exact/fs_ca_refl.
    apply/on_can_inj; exact/K.
  - by exists g; rewrite lFsPrePoset.build_eventset.
  - move=> e; rewrite ?fs_labE lFsPrePoset.build_lab /sub_lift.
    case: insubP=> /= [[/=>?]|].
    + by rewrite /fl -labf fs_labE /= K' // => _ -> //.
    by rewrite -fs_labNbotE negbK=>/eqP->.
  move=>>; rewrite ?/(_ <= _) /= lFsPrePoset.build_cov_ca // /ca /fE.
  rewrite lFsPrePoset.build_eventset // => ??.
  case/orP=> [/eqP->|]; first exact/fs_ca_refl.
  case/and3P=> /orP[/eqP->*|]; first exact/fs_ca_refl.
  by case/and3P=> /homf; rewrite !(Hom.mono_lab_eventset _ labf) ?K' //.
Qed.

Definition upd_iso (f : E1 -> E2) p q e' x y e :=
 if e \in lfsp_eventset p then f e else if e == x then y else e'.

Section Update.
Variables (f : E1 -> E2) (p : lfsposet E1 L) (q : lfsposet E2 L).
Variables (e' : E2) (x : E1) (y : E2).

Hypothesis (en' : e' \notin lfsp_eventset q).
Hypothesis (xn  : x  \notin lfsp_eventset p).
Hypothesis (yn  : y  \notin lfsp_eventset q).
Hypothesis (neq : e' != y).

Local Notation upd_iso f := (upd_iso f p q e' x y).

Lemma upd_iso_supp e :
  e \in lfsp_eventset p -> upd_iso f e = f e.
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
    by rewrite -(Hom.mono_lab_eventset _ labf)=> /negP.
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
  by rewrite -(Hom.mono_lab_eventset _ labf) => ->.
Qed.

End Update.

End hEquiv.

Section Equiv.
Context (E : identType) (L : botType).
Implicit Types (p q : lfsposet E L).

(* TODO: generalize the proofs to arbitary `T -> T -> Type`? *)
Lemma iso_eqv_refl : reflexive (@iso_eqv E E L).
Proof.
  move=> p; apply/lFinPoset.Iso.iso_eqvP.
  exists; exact/[iso of idfun].
Qed.

Lemma iso_eqv_sym : symmetric (@iso_eqv E E L).
Proof.
  move=> p q.
  apply/idP/idP=> /lFinPoset.Iso.iso_eqvP [f];
    apply/lFinPoset.Iso.iso_eqvP;
    exists; exact/[iso of bhom_inv f].
Qed.

Lemma iso_eqv_trans : transitive (@iso_eqv E E L).
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

(* TODO: unfortunately, due to current representation of 
 *   posets it is not possible to prove the lemma in 
 *   the other direction. It is because the posets 
 *   are represented as an arbitary relation, 
 *   and thus two non-isomorphic relations
 *   can have isomorphic transitive closures. 
 *   We should try to overcome this by changing the representation. 
 *)
Lemma rename_iso f p :
  iso_eqv p (lFsPoset.rename f p).
Proof.
  move: (lfsp_supp_closed p)=> supcl.
  move: (lfsp_acyclic p)=> acyc.
  rewrite iso_eqv_sym.
  apply/iso_eqvP; exists f; split.
  - by move=> e /=; rewrite !fs_labE lFsPrePoset.rename_lab /= fperm_invK. 
  - by move=> x y; rewrite !fs_caE lFsPrePoset.rename_ca /= ?fperm_invK.
  exact/onW_bij/fperm_bij.
Qed.  

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
Context {E : identType} {L : botType}.

Canonical iso_equiv_rel :=
  EquivRel iso_eqv
    (@iso_eqv_refl E L)
    (@iso_eqv_sym E L)
    (@iso_eqv_trans E L).

Definition pomset := {eq_quot iso_eqv}.

Canonical pomset_quotType := [quotType of pomset].
Canonical pomset_eqType := [eqType of pomset].
Canonical pomset_choiceType := [choiceType of pomset].
Canonical pomset_eqQuotType := [eqQuotType iso_eqv of pomset].

Definition pom : lfsposet E L -> pomset := \pi.

Implicit Types (p : pomset).

Coercion lfsposet_of p : lfsposet E L := repr p.

(* TODO: specialize lemma event further? use is_iso equivalence directly? *)
Lemma pomP q :
  pi_spec pomset_quotType q (repr (pom q)).
Proof. by case: piP. Qed.

End Def.
End Def.

Arguments pomset E L : clear implicits.

Section OfSeq.
Context (E : identType) (L : botType).
Implicit Types (p : pomset E L).
Implicit Types (ls : seq L).

Definition of_seq ls : pomset E L :=
  pom (@lFsPoset.of_seq E L ls).

End OfSeq.

Section InterRel.
Context (E : identType) (L : botType).
Implicit Types (p : pomset E L).

Variable (r : rel E).
Hypothesis (refl  : reflexive r).
Hypothesis (trans : transitive r).

Definition inter_rel p : pomset E L :=
  \pi (lFsPoset.inter_rel r refl trans p).

End InterRel.

Arguments inter_rel {E L} r.

Section Inter.
Context (E : identType) (L : botType).
Implicit Types (p q : pomset E L).

Definition inter p q : pomset E L :=
  \pi (lFsPoset.inter p q).

End Inter.

Section Restrict.
Context (E : identType) (L : botType).
Implicit Types (P : pred E).
Implicit Types (p q : pomset E L).

Definition restrict P p : pomset E L :=
  \pi (lFsPoset.restrict P p).

End Restrict.


Section Relabel.
Context (E : identType) (L1 L2 : botType).
Implicit Types (f : L1 -> L2).
Implicit Types (p : pomset E L1).

Definition relabel f p : pomset E L2 :=
  \pi (@lFsPoset.relabel E L1 L2 f p).

End Relabel.

Arguments relabel {E L1 L2} f p.

Import lPoset.Syntax.
Import lFsPoset.Syntax.

Module Export iHom.
Module Export POrder.
Section POrder.
Implicit Types (E : identType) (L : botType).

Lemma pom_ihom_le E1 E2 L (p : lfsposet E1 L) (q : lfsposet E2 L) :
  ihom_le (repr (pom p)) (repr (pom q)) = ihom_le p q.
Proof.
  rewrite /ihom_le.
  case: pomP=> q' /eqmodP/lFinPoset.Iso.iso_eqvP[f].
  case: pomP=> p' /eqmodP/lFinPoset.Iso.iso_eqvP[g].
  apply/lFinPoset.iHom.ihom_leP/lFinPoset.iHom.ihom_leP=> [][h]; exists.
  - exact/[ihom of g \o h \o [iso of (bhom_inv f)]].
  exact/[ihom of [iso of (bhom_inv g)] \o h \o f].
Qed.

Context {E : identType} {L : botType}.
Implicit Types (p q : pomset E L).

Lemma pom_ihom_mono :
  {mono (@pom E L) : p q / ihom_le p q >-> ihom_le (repr p) (repr q)}.
Proof. exact/pom_ihom_le. Qed.

Canonical ihom_le_quot_mono2 := PiMono2 pom_ihom_mono.

(* TODO: porder instance for ihom_le *)

End POrder.
End POrder.
End iHom.

Module Export bHom.
Module Export POrder.
Section POrder.
Implicit Types (E : identType) (L : botType).

Lemma pom_bhom_le E1 E2 L (p : lfsposet E1 L) (q : lfsposet E2 L) :
  bhom_le (repr (pom p)) (repr (pom q)) = bhom_le p q.
Proof.
  rewrite /bhom_le.
  case: pomP=> q' /eqmodP/lFinPoset.Iso.iso_eqvP[f].
  case: pomP=> p' /eqmodP/lFinPoset.Iso.iso_eqvP[g].
  apply/lFinPoset.bHom.bhom_leP/lFinPoset.bHom.bhom_leP=> [][h]; exists.
  - exact/[bhom of g \o h \o [iso of bhom_inv f]].
  exact/[bhom of [iso of bhom_inv g] \o h \o f].
Qed.

Lemma pom_bhom_le1 E1 E2 L (p : lfsposet E1 L) (q : lfsposet E2 L) :
  bhom_le p (repr (pom q)) = bhom_le p q.
Proof.
  rewrite /bhom_le.
  case: pomP=> q' /eqmodP/lFinPoset.Iso.iso_eqvP[f].
  (* case: pomP=> p' /eqmodP/lFinPoset.fisoP[g]. *)
  apply/lFinPoset.bHom.bhom_leP/lFinPoset.bHom.bhom_leP=> [][h]; exists.
  - exact/[bhom of h \o [iso of (bhom_inv f)]].
  exact/[bhom of h \o f].
Qed.

Context {E : identType} {L : botType}.
Implicit Types (p q : pomset E L).

Lemma pom_bhom_mono :
  {mono (@pom E L) : p q / bhom_le p q >-> bhom_le (repr p) (repr q)}.
Proof. exact/pom_bhom_le. Qed.

Lemma pom_lin_mono l :
  {mono (@pom E L) : p / l \in lin p >-> l \in lin (repr p)}.
Proof. exact/pom_bhom_le1. Qed.

Canonical bhom_le_quote_mono2 := PiMono2 pom_bhom_mono.
Canonical lin_quote_mono2 l := PiMono1 (pom_lin_mono l).

Lemma pom_bhom_le_refl :
  reflexive (@bhom_le E E L : rel (pomset E L)).
Proof. exact/bhom_le_refl. Qed.

Lemma pom_bhom_le_antisym :
  antisymmetric (@bhom_le E E L : rel (pomset E L)).
Proof.
  move=> p q; rewrite -[p]reprK -[q]reprK !piE.
  move=> /andP[??]; exact/eqmodP/iso_bhom_le_antisym.
Qed.

Lemma pom_bhom_le_trans :
  transitive (@bhom_le E E L : rel (pomset E L)).
Proof. exact/bhom_le_trans. Qed.

Lemma disp : unit.
Proof. exact: tt. Qed.

Definition pomset_bhomPOrderMixin :=
  @LePOrderMixin _
    (@bhom_le E E L : rel (pomset E L))
    (fun p q => (q != p) && (bhom_le p q))
    (fun p q => erefl) pom_bhom_le_refl pom_bhom_le_antisym pom_bhom_le_trans.

Canonical pomset_bhomPOrderType :=
  POrderType disp (pomset E L) pomset_bhomPOrderMixin.

Lemma pom_bhom_leE p q : p <= q = bhom_le p q.
Proof. done. Qed.

End POrder.
End POrder.
End bHom.

Module Export Theory.
Section Theory.
Context {E : identType} {L : botType}.
Implicit Types (p q : pomset E L).

Lemma iso_eqv_pom (p : lfsposet E L) :
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
Context (E : identType) (L : botType).

Structure tomset : Type := mkTomset {
  tomset_val :> pomset E L;
  _ : totalb (fin_ca tomset_val);
}.

Canonical tomset_subType := Eval hnf in [subType for tomset_val].

Implicit Types (t : tomset) (ls : seq L).

Lemma tomset_total t :
  total (<=%O : rel [FinEvent of t]).
Proof. by move: (valP t)=> /totalP. Qed.

Lemma tomset_total_in t :
  {in (lfsp_eventset t) &, total (<=%O : rel [Event of t])}.
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

Arguments tomset E L : clear implicits.


Section OfSeq.
Context (E : identType) (L : botType).
Implicit Types (p : lfspreposet E L).
Implicit Types (ls : seq L).

Lemma of_seq_total ls :
  let p := @Pomset.of_seq E L ls in
  total (fin_ca p).
Proof.
  pose p := @lFsPoset.of_seq E L ls.
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
Context {E : identType} {L : botType}.
Implicit Types (t u : tomset E L).

Lemma tomset_labelsK :
  cancel (@lfsp_labels E L : tomset E L -> seq L) (@of_seq E L).
Proof.
  move=> t; apply/val_inj/esym/eqP=> /=.
  rewrite eqquot_piE iso_eqv_sym.
  apply/iso_eqvP.
  pose u := lFsPoset.of_seq E L (lfsp_labels t).
  pose f : [Event of t] -> [Event of u] :=
    fun e => decode (lfsp_idx t e).
  move: (lfsp_labels_Nbot t)=> labD.
  have usz : lfsp_size u = lfsp_size t.
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
    + rewrite e1In e2In leEnat=> /lfsp_idx_le -> //; exact/lfsp_acyclic.
    + move=> /eqP /decode_inj /lfsp_idx_inj -> //; exact/fs_ca_refl.
    move=> /and3P[le12 ??].
    move: (tomset_total_in e1In e2In).
    rewrite !fs_caE=> /orP[|] //.
    move=> /(lfsp_idx_le (lfsp_acyclic _)) le21.
    suff->: e1 = e2 by exact/fs_ca_refl.
    by apply/(lfsp_idx_inj e1In e2In)/le_anti/andP.
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

