From Coq Require Import Relations.
From RelationAlgebra Require Import lattice monoid rel boolean kat_tac.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat seq tuple.
From mathcomp Require Import eqtype choice order generic_quotient.
From mathcomp Require Import fintype finfun finset fingraph finmap zify.
From mathcomp.tarjan Require Import extra acyclic kosaraju acyclic_tsorted. 
From eventstruct Require Import utils rel relalg inhtype order ident.
From eventstruct Require Import lts lposet pomset.

(******************************************************************************)
(* This file contains a theory connecting pomset languages and                *)
(* labeled transition systems.                                                *)
(* TODO.                                                                      *)
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
Local Open Scope pomset_scope.


(* TODO: consider decidable/bool languages only? *)
Notation pomlang E L bot := (pomset E L bot -> Prop).

Module Export PomLang.
Section PomLang.
Context (E : identType) (L : choiceType) (bot : L).
Context (S : ltsType L).
Implicit Types (l : L) (s : S).
Implicit Types (p : pomset E L bot).

(* TODO: this should be simplified *)
Definition lts_pomlang s : pomlang E L bot := 
  fun p => exists2 ls, p = @Pomset.of_seq E L bot ls & lts_lang s ls. 

(* TODO: for bool-languages it can be stated using {subsumes} notation *)
Definition subsumes : pomlang E L bot -> pomlang E L bot -> Prop := 
  fun P Q => forall p, P p -> exists q, Q q /\ bhom_le p q.

(* TODO: for bool-languages it can be stated using {subsumes} notation *)
Definition supports : pomlang E L bot -> pomlang E L bot -> Prop := 
  fun P Q => forall p, P p -> exists q, Q q /\ bhom_le q p.

End PomLang.
End PomLang.

(* TODO: remove these notations? *)
Notation "P '\subsumes' Q" := (subsumes P Q) (at level 40, no associativity).
Notation "P '\supports' Q" := (supports P Q) (at level 40, no associativity).


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

Lemma add_event_fs_sizeE : 
  fs_size (lfspre_add_event l es p) = 
  (fs_size p).+1.
Proof. rewrite /fs_size add_event_finsuppE cardfsU1 fresh_seq_nmem; lia. Qed.

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

Lemma add_event_freshE :
  lfsp_fresh (lfspre_add_event l es p) = fresh (lfsp_fresh p).
Proof. 
  rewrite /lfsp_fresh add_event_finsuppE fresh_seq_add.
  rewrite /lfsp_fresh max_l //.
  exact/ltW/fresh_lt.
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
  | ReflectT pf => lFsPoset
    (let: conj lD esSub := andP pf in
    let labD  := add_event_lab_defined es lD (lfsp_lab_defined p) in
    let supcl := add_event_supp_closed lD esSub (lfsp_supp_closed p) in
    let acyc  := add_event_acyclic lD esSub 
                   (lfsp_supp_closed p) 
                   (lfsp_acyclic p) 
    in
     (introT and3P (And3 labD supcl acyc)))
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

Lemma lfsp_add_eventE l es p : l != bot -> (es `<=` finsupp p) ->
  (* --- *)
  ((finsupp (lfsp_add_event l es p) =  lfsp_fresh p |` finsupp p)               *
  (* --- *)
  (fs_lab (lfsp_add_event l es p)   =1 fun e =>
    if e == lfsp_fresh p then l else fs_lab p e))                               *
  (* --- *)
  ((fs_rcov (lfsp_add_event l es p) =1 fun e =>
    if e == lfsp_fresh p then es else fs_rcov p e)                              *
  (* --- *)
  (fs_ica (lfsp_add_event l es p)   =2 fun e1 e2 => 
    (e1 \in es) && (e2 == lfsp_fresh p) || (fs_ica p e1 e2)))                   *
  (* --- *)
  (fs_ca (lfsp_add_event l es p)    =2 fun e1 e2 =>
    (e1 \in lfsp_dw_clos p es) && (e2 == lfsp_fresh p) || (fs_ca p e1 e2))      * 
  (* --- *)
  (fs_size (lfsp_add_event l es p) = (fs_size p).+1)                            *
  (* --- *)
  (lfsp_fresh (lfsp_add_event l es p) = fresh (lfsp_fresh p)).
Proof.
  rewrite ?/lfsp_add_event; (do ? case: eqP=> //=)=>*.
  rewrite add_event_finsuppE //; do ? split=> //>;
  rewrite (add_event_fs_labE,
           add_event_fs_icaE,
           add_event_fs_rcovE,
           add_event_fs_caE,
           add_event_fs_sizeE,
           add_event_freshE)
    //; case: (p)=> /=> /and3P[] //.
Qed.

Notation of_seq := (lFsPoset.of_seq E L bot).

Hint Resolve lfsp_supp_closed lfsp_acyclic : core.

Lemma lfsp_trace_labels_defined tr : 
  bot \notin labels tr.
Proof. 
  case: tr=> /= ? /andP[/allP /= i ?].
  apply/mapP=>-[/= [> /i + ?]]. 
  case/lfsp_ltransP=> /eqP + ?; exact.
Qed.

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
  tr \in trace_lang emp -> lfsp_fresh p = iter (size tr) fresh \i0.
Proof.
  case: tr=> /= t it; rewrite /trace_lang /(_ \in _) /==>->.
  elim/last_ind: t it=> //= [_ _|].
  - by rewrite /lfsp_fresh /lFsPrePoset.empty finsupp0 /fresh_seq.
  move=> t [l s1 s2] IHt. 
  rewrite is_trace_rcons=> /and3P[].
  case/lfsp_ltransP=> /= lD [es esSub eq'] /[swap] adj. 
  move=> tTrace /eqP tFst.
  rewrite lst_state_rcons size_rcons /=.
  rewrite -IHt //=; last first.
  - rewrite eq_sym; exact/eqP/fst_state_rcons_belast/esym/tFst.
  rewrite eq' lfsp_add_eventE //.
  by rewrite (lst_state_rcons_adj tFst).
Qed. 
>>>>>>> re(pomset_lts): fixing & simplifying proofs

Lemma lfsp_trace_finsupp tr :
  let emp := lFsPoset.empty E L bot in
  let p := lst_state emp tr in
  tr \in trace_lang emp -> finsupp p = [fset e | e in nfresh \i0 (size tr)].
Proof.
  case: tr=> /= t it; rewrite /trace_lang /(_ \in _) /=.
  elim/last_ind: t it=> //= [_ _|].
  - by apply/fsetP=> ?; rewrite finsupp0 ?inE.
  move=> t [l s1 s2] IHt. 
  rewrite is_trace_rcons=> /and3P[].
  case/lfsp_ltransP=> /= lD [es esSub eq'] /[swap] adj. 
  move=> tTrace /eqP tFst.
  rewrite lst_state_rcons /= size_rcons.
  rewrite nfreshSr -[in rcons (nfresh _ _) _]cats1 fset_cat fset_singl /=. 
  rewrite -IHt //=; last first.
  - rewrite eq_sym; exact/eqP/fst_state_rcons_belast/esym/tFst.
  rewrite eq' lfsp_add_eventE //.
  rewrite (lst_state_rcons_adj tFst) //=.
  suff->: lfsp_fresh s1 = iter (size t) fresh \i0 => //.
  - by rewrite fsetUC.
  rewrite (@lfsp_trace_fresh (Trace tTrace)) //=. 
  - by rewrite (lst_state_rcons_adj tFst).
  by rewrite unfold_in {1}(fst_state_rcons_adj tFst).
Qed. 

Lemma lfsp_trace_lab tr e : 
  let emp := lFsPoset.empty E L bot in 
  let p := lst_state emp tr in
  tr \in trace_lang emp -> fs_lab p e = nth bot (map lbl tr) (encode e).
Proof.
  case: tr=> /= t it; rewrite /trace_lang /(_ \in _) /=.
  elim/last_ind: t it=> //= [_ _|].
  - rewrite lFsPrePoset.fs_lab_empty. 
    by case: (encode _)=> //= ?; rewrite nth_nil.
  move=> t [l s1 s2] IHt. 
  rewrite is_trace_rcons=> /and3P[].
  case/lfsp_ltransP=> /= lD [es esSub eq'] /[swap] adj. 
  move=> tTrace /eqP tFst.
  rewrite lst_state_rcons /=.
  rewrite map_rcons nth_rcons /= size_map.
  rewrite eq' lfsp_add_eventE //. 
  rewrite (@lfsp_trace_fresh (Trace tTrace)); last first.
  - by rewrite unfold_in {1}(fst_state_rcons_adj tFst).
  - by rewrite (lst_state_rcons_adj tFst).
  rewrite -(inj_eq encode_inj) /= ?(encode_fresh, encode_iter) encode0 add0n.
  case: ifP=> [/eqP->|/eqP nEq]; first by rewrite ltnn.
  have->: s1 = src (mk_step l s1 s2) by done. 
  rewrite -(lst_state_rcons_adj tFst) //.
  rewrite IHt //; last first.
  - by rewrite {1}(fst_state_rcons_adj tFst).
  case: ifP=> //= ?; rewrite nth_default //= size_map; lia.  
Qed.

Lemma lfsp_lang_lin tr : 
  let emp := lFsPoset.empty E L bot in 
  let p := lst_state emp tr in
  tr \in trace_lang emp -> labels tr \in lin p.
Proof. 
  move=> emp p inTr; rewrite /lin inE /=.
  pose q := lFsPoset.of_seq E L bot (map lbl tr).
  have labsD : bot \notin (map lbl tr).
  - apply/mapP=> -[[/=> /(allP (trace_steps _))/[swap]<-]].
    by case/lfsp_ltransP=> /eqP.
  (* rewrite -/q /=; apply/bhom_leP=> /=. *)
  (* - exists id; split=> //; last by exists id. *)
  (* repeat constructor. *)
  (* - move=> e; rewrite !fs_labE. *)
  (*   rewrite lFsPoset.of_seq_valE labsD ?lFsPrePoset.of_seq_labE //=. *)
  (*   by rewrite lfsp_trace_lab. *)
  (* move=> e1 e2; rewrite !fs_caE. *)
  rewrite -/q /=; apply/bhom_leP=> /=. 
  unshelve eexists; first (unshelve econstructor); first exact: id; last first.  
  - by move=> /=; exists id.
  (repeat constructor)=> [e | e1 e2]; rewrite ?fs_labE ?fs_caE.
  - by rewrite lFsPoset.of_seq_valE labsD lFsPrePoset.of_seq_labE lfsp_trace_lab.
  rewrite lFsPoset.of_seq_valE labsD ?lFsPrePoset.of_seq_fs_caE //.
  rewrite !lFsPrePoset.of_seq_finsupp //=.
  rewrite !in_fset /= !size_labels.
  move: (lfsp_supp_closed p)=> supcl.
  move: (lfsp_acyclic p)=> acyc.
  move=> /[dup] + /(supp_closed_ca supcl acyc) /orP[->|/andP[]] //.
  rewrite lfsp_trace_finsupp // !inE => ???.
  apply/orP; right; apply/and3P; split=> //.
  apply/(fs_ca_ident_le supcl acyc)=> //.
  exact/(invariant_trace_lan invariant_operational)/opetaional0.
Qed.

Lemma lfsp_lin_trace_lang tr : 
  let emp := lFsPoset.empty E L bot in 
  let p := lst_state emp tr in
  labels tr \in lin p -> tr \in trace_lang emp.
Proof.
  move=> /=; rewrite /trace_lang ?/(_ \in _) /= /lin /=.
  move/bhom_le_size; rewrite lFsPoset.of_seq_size size_map.
  rewrite lfsp_trace_labels_defined.  
  move=> sizeE; apply/eqP/esym/val_inj/lFsPrePoset.eq_emptyE=> /=.
  set f := [eta (@fs_size E L bot)]: lfsposet _ _ _ -> nat.
  move: (@measure_lst _ _ _ f S) sizeE=> /=; rewrite /f /= /==> -> //.
  - rewrite iter_succn; lia.
  move=> s s' l.
  case/lfsp_ltransP=> ? [?? ->]. 
  by rewrite lfsp_add_eventE.
Qed.

Lemma max_of_seq (ls : seq L): 
  bot \notin ls ->
  (if ls == [::] then fset0 else [fset iter (size ls).-1 fresh \i1])
  `<=` finsupp (lFsPoset.of_seq E L bot ls).
Proof.
  move=> ?.
  rewrite /= lFsPoset.of_seq_valE // lFsPrePoset.of_seq_finsupp //.
  case: (ls)=> //= ? l'.
  rewrite fsub1set ?inE in_nfresh encode_iter encode_fresh encode1.
  case: l'=> //=*; rewrite ?eqxx; lia.
Qed.

Lemma of_seq_rcons l ls: 
  bot \notin ls ->
  l != bot ->
  lFsPoset.of_seq E L bot (rcons ls l) = 
  lfsp_add_event 
    l
    (if ls == [::] then fset0 else [fset iter (size ls).-1 fresh \i1])
    (lFsPoset.of_seq E L bot ls).
Proof.
  move=> nls nl; apply/eqP/lfsposet_eqP.
  have?: bot \notin rcons ls l by rewrite mem_rcons ?inE negb_or eq_sym nls nl.
  split=> x>; rewrite lfsp_add_eventE ?max_of_seq ?lFsPoset.of_seq_valE //.
  all: rewrite lFsPrePoset.of_seq_fresh //.
  - rewrite ?lFsPrePoset.of_seq_labE -rcons_cons nth_rcons /=.
    rewrite -[x == _](inj_eq (encode_inj)) encode_iter encode1 add1n.
    case: ltngtP=> // ?; rewrite nth_default //=; lia.
  have ?: bot != l by rewrite eq_sym.
  case: ifP=> [/eqP->|];
  rewrite ?lFsPrePoset.of_seq_fs_icaE ?lFsPrePoset.of_seq_finsupp ?inE //=.
  - rewrite ?inE andbF; (do ? case: (_ =P _)=> //)=>->-> /(congr1 encode).
    rewrite encode_fresh; lia.
  rewrite -size_eq0 -[fresh _ == _](inj_eq (encode_inj)).
  do 2 rewrite -[_ == iter _ _ _](inj_eq (encode_inj)).
  rewrite ?in_nfresh ?encode_iter ?encode1 ?encode_fresh size_rcons.
  case: (size ls)=> //=; lia.
Qed.

Lemma is_sup_fresh (X : {fset E}) : 
  is_sup (fresh_seq X |` X) (fresh_seq X).
Proof.
  apply/is_supP; split=>>; rewrite ?inE ?eqxx //.
  by move=> /orP[/eqP->|/fresh_seq_mem/ltW].
Qed.

Lemma operational_of_seq ls : 
  bot \notin ls ->
  operational (of_seq ls).
Proof.
  move=> ?; apply/operationalP=>>.
  - exact/lfsp_supp_closed.
  - exact/lfsp_acyclic.
  rewrite lFsPoset.of_seq_valE // lFsPrePoset.of_seq_fs_caE //.
  by case/orP=> [/eqP->|/andP[->]].
Qed.

Section BackwardStep.
Context (p : lfsposet E L bot) (n : nat).
Hypothesis oper : operational p.
Hypothesis fs_p : finsupp p = [fset e | e in nfresh \i1 n].
Hypothesis ne0n : n != 0%N.

Let e : E := iter n.-1 fresh \i1.

(* TODO: move to lFsPoset.Theory *)
Lemma emax : [forall y : finsupp p, ~~ fs_ica p e (val y)].
Proof.
  apply/forallP=> -[]/= ?; rewrite fs_p ?inE /= in_nfresh encode1=> ?; apply/negP.
  move/(operational_fs_sca (lfsp_supp_closed _) (lfsp_acyclic _)): oper.
  move/[swap]/(@t_step E (fs_ica p)).
  move/(fs_scaP _ _ (lfsp_supp_closed _) (lfsp_acyclic _)).
  move/[swap]/[apply]; rewrite /(_ <^i _) /= /Ident.Def.ident_lt /e.
  rewrite encode_iter encode1; lia.
Qed.

(* TODO: remove hint? *)
Hint Resolve emax : core.

Lemma fresh_del : lfsp_fresh (lFsPoset.delete p e) = e.
Proof.
  case: (n =P 1%N) fs_p emax=> [|?].
  - rewrite /e=>-> /= fsp ?; rewrite /lfsp_fresh lFsPoset.lfsp_delE // fsp.
    have: ([fset e | e in [:: \i1]] `\ \i1 =i ([::] : seq E)).
    - by move=>>; rewrite ?inE; case: (_ =P _).
    rewrite /fresh_seq /=; move/(max_set_eq (@i0_min _))->.
    by rewrite /= fresh0.
  rewrite /lfsp_fresh lFsPoset.lfsp_delE // fs_p.
  have: [fset e' | e' in nfresh \i1 n] `\ e =i nfresh \i1 n.-1.
  - move=>>; rewrite ?inE /= /e ?in_nfresh -(inj_eq encode_inj) encode_iter.
    rewrite encode1; lia.
  rewrite /fresh_seq=> /(max_set_eq (@i0_min _))->*.
  apply/fresh_seq_nfresh; lia. 
Qed.

Lemma backward_step : 
  exists q, q --[fs_lab p e]--> p.
Proof.
  exists (lFsPoset.delete p e); apply/lfsp_ltransP.
  have nb: (fs_lab p e != bot).
  - rewrite fs_labNbot fs_p ?inE /= /e in_nfresh encode_iter encode1; lia.
  split=> //.
  have ess: (p e).2 `<=` finsupp (lFsPoset.delete p e).
  - rewrite lFsPoset.lfsp_delE //; apply/fsubsetP=> x /[dup]; rewrite ?inE.
    move/supp_closedP/(_ x e): (lfsp_supp_closed p)=>/[apply]-[-> _].
    have ic: (irreflexive (fin_ica p)) by apply/acyc_irrefl/lfsp_acyclic.
    move/(_ e): (fs_ica_irrefl (lfsp_supp_closed p) ic).
    rewrite /fs_ica/=/fs_rcov; by case: (_ =P _)=> [->->|].
  exists (p e).2=> //; apply/val_inj; rewrite /lfsp_add_event /=.
  case: eqP=> /= [_|]; last by rewrite nb.
  rewrite /lfspre_add_event fresh_del /lFsPoset.delete.
  case: eqP=>//= [_|/(_ emax)] //.
  apply/fsfunP=>>; rewrite ?fsfun_withE /fs_lab. 
  case: (_ =P _)=> //->; by case: (p e). 
Qed.

End BackwardStep.

Lemma lfsp_lin_lang p (ls : seq L) : 
  let emp := lFsPoset.empty E L bot in 
  bot \notin ls ->
  lFsPoset.Hom.axiom p (of_seq ls) id ->
  exists2 tr : trace _,
      lst_state p tr = p & 
      labels tr = ls.
Proof.
  elim/last_ind: ls p=>/=; first by exists [trace].
  move=> ls l IHl p nb ax.
  case: (@backward_step p (size ls).+1).
  - exact/(hom_operational ax)/operational_of_seq.
  - rewrite -(finsupp_hom_id ax) lFsPoset.of_seq_valE //.
    by rewrite lFsPrePoset.of_seq_finsupp // size_rcons.
  - lia.
  move=> q.
  pose n := (size ls).+1.
  pose e : E := iter n.-1 fresh \i1.
  have->: fs_lab p e = l.
  - case: ax=> /(_ e); rewrite ?fs_labE /=.
    rewrite lFsPoset.of_seq_valE // lFsPrePoset.of_seq_labE.
    rewrite encode_iter encode1 /= nth_rcons /=.
    case: ifP; first lia; by rewrite eqxx.
  move=> str; move: nb ax.
  rewrite mem_rcons ?inE negb_or=> /andP[/[1! eq_sym]??].
  rewrite of_seq_rcons // => ax.
  have?: 
    (if ls == [::] then fset0 else [fset iter (size ls).-1 fresh \i1])
    `<=` finsupp (lFsPoset.of_seq E L bot ls).
  - exact/max_of_seq.
  move: (str); case/lfsp_ltransP=> ?[es ?/[dup] pE->].
  move/finsupp_hom_id: (ax).
  rewrite pE ?lfsp_add_eventE // => fE.
  have fqE: lfsp_fresh (of_seq ls) = lfsp_fresh q.
  - apply/(@is_sup_uniq _ _ (lfsp_fresh q |` finsupp q));
    first rewrite -?fE; exact/is_sup_fresh.
  have fsE: finsupp q = finsupp (of_seq ls).
  - apply/fsetP=> x; move/fsetP/(_ x): fE; rewrite ?inE fqE.
    case: (x =P _)=> //->_; by rewrite -{2}fqE ?(negbTE (fresh_seq_nmem _)).
  case: (IHl q)=> //.
  - move: ax; rewrite /lFsPoset.Hom.axiom /lab ?fs_labE /==> -[lf lc]; split.
    + move: lf=> /[swap] x /(_ x); rewrite pE ?lfsp_add_eventE // fqE.
      case: ifP=> // /eqP-> _.
      by rewrite ?fs_lab_bot // -?fsE /lfsp_fresh fresh_seq_nmem.
    + move: lc=> /[swap] e1 /(_ e1)/[swap] e2 /(_ e2) /[swap]in1/[swap] in2.
      have /negbTE nf: e2 != lfsp_fresh q. 
      * apply/eqP; move: in2=> /[swap]->.
        by rewrite (negbTE (fresh_seq_nmem _)).
      rewrite ?/(_ <= _) /= pE ?lfsp_add_eventE // fqE nf ?andbF /= ?inE.
      rewrite in1 in2 ?orbT; exact.
  move=> tr lstE labE.
  have it: is_trace (rcons tr (mk_step l q p)).
  - rewrite is_trace_rcons; apply/and3P; split=> //; first by case: (tr).
    by rewrite adjoint_lastE /= lstE.
  exists (Trace it)=> /=; rewrite ?lst_state_rcons // /labels map_rcons.
  exact/congr2.
Qed.

End Theory.
End Theory.  

End lFsPosetLTS.

