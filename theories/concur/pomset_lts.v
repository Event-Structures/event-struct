From Coq Require Import Relations.
From RelationAlgebra Require Import lattice monoid rel boolean kat_tac.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat seq tuple.
From mathcomp Require Import eqtype choice order generic_quotient.
From mathcomp Require Import fintype finfun finset fingraph finmap zify.
From mathcomp.tarjan Require Import extra acyclic kosaraju acyclic_tsorted. 
From eventstruct Require Import utils seq rel relalg inhtype order ident ilia.
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
Notation pomlang E L := (pomset E L -> Prop).

Module Export PomLang.
Section PomLang.
Context (E : identType) (L : botType).
Context (S : ltsType L).
Implicit Types (l : L) (s : S).
Implicit Types (p : pomset E L).

(* TODO: this should be simplified *)
Definition lts_pomlang s : pomlang E L := 
  fun p => exists2 ls, p = @Pomset.of_seq E L ls & lts_lang s ls. 

(* TODO: for bool-languages it can be stated using {subsumes} notation *)
Definition subsumes : pomlang E L -> pomlang E L -> Prop := 
  fun P Q => forall p, P p -> exists q, Q q /\ bhom_le p q.

(* TODO: for bool-languages it can be stated using {subsumes} notation *)
Definition supports : pomlang E L -> pomlang E L -> Prop := 
  fun P Q => forall p, P p -> exists q, Q q /\ bhom_le q p.

(* for a given pomset p returns language consisting of 
 * restrictions of p onto its principal ideals, 
 * that is prefixes of events of p.  
 *)
Definition pideal_lang p : pomlang E L := 
  let pideals := [fset (pideal (e : [Event of p])) | e in finsupp p] in
  let qs := [fset (Pomset.restrict (mem (es : {fset E})) p) | es in pideals] in
  fun q => q \in qs.

End PomLang.
End PomLang.

(* TODO: remove these notations? *)
Notation "P '\subsumes' Q" := (subsumes P Q) (at level 40, no associativity).
Notation "P '\supports' Q" := (supports P Q) (at level 40, no associativity).


Module Export AddEvent.

Module Export Def.
Section Def.  
Context (E : identType) (L : botType).
Implicit Types (l : L) (es : {fset E}).
Implicit Types (p : lfspreposet E L).

Definition lfspre_add_event l es p : lfspreposet E L := 
  let e := lfsp_fresh p in
  [fsfun p with e |-> (l, es)].

End Def.
End Def.

Module Export Theory.
Section Theory.  
Context (E : identType) (L : botType).
Variable (l : L) (es : {fset E}).
Variable (p : lfspreposet E L).

Hypothesis (lD : l != bot).
Hypothesis (esSub : es `<=` lfsp_eventset p).

Lemma add_event_fs_labE e :
  fs_lab (lfspre_add_event l es p) e = 
    if e == lfsp_fresh p then l else fs_lab p e. 
Proof. by rewrite /fs_lab /lfspre_add_event fsfun_withE; case: ifP. Qed.

Lemma add_event_eventsetE :
  lfsp_eventset (lfspre_add_event l es p) = (lfsp_fresh p) |` (lfsp_eventset p).
Proof. 
  apply/fsetP=> e; rewrite /lfspre_add_event /lfsp_eventset. 
  rewrite !inE finsupp_with xpair_eqE add_event_fs_labE /=.
  move: lD=> /negPf -> /=; rewrite !inE; by case: ifP.
Qed.

Lemma add_event_fs_sizeE : 
  lfsp_size (lfspre_add_event l es p) = (lfsp_size p).+1.
Proof. rewrite /lfsp_size add_event_eventsetE cardfsU1 fresh_seq_nmem; lia. Qed.

Lemma add_event_fs_rcovE e :
  fs_rcov (lfspre_add_event l es p) e = 
    if e == lfsp_fresh p then es else fs_rcov p e. 
Proof. by rewrite /fs_rcov /lfspre_add_event fsfun_withE; case: ifP. Qed.

Lemma add_event_fs_icaE e1 e2 : supp_closed p ->
  fs_ica (lfspre_add_event l es p) e1 e2 = 
    (e1 \in es) && (e2 == lfsp_fresh p) || (fs_ica p e1 e2).
Proof. 
  move=> /supp_closedP supcl. 
  rewrite /fs_ica /= !add_event_fs_rcovE.
  case: ifP=> [/eqP->|]; last by rewrite andbF.
  rewrite andbT orb_idr // => /supcl [].
  by move: (fresh_seq_nmem (lfsp_eventset p))=> /negP.  
Qed.

Lemma add_event_supp_closed :
  supp_closed p -> supp_closed (lfspre_add_event l es p).
Proof.  
  move=> supcl.
  apply/supp_closedP=> e1 e2.
  rewrite add_event_eventsetE //.
  rewrite add_event_fs_icaE // !in_fset1U. 
  move=> /orP[/andP[]|].
  - move=> in1 /eqP ->. 
    rewrite eqxx orTb; split=> //.
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
    by move: (fresh_seq_nmem (lfsp_eventset p))=> /negP.
  have->: r1^* ≡ 1 ⊔ r1.
  - rewrite str_unfold_l; apply/qmk_weq.
    rewrite str_unfold_l dotxpls dotA.
    have->: r1 ⋅ r1 ≡ 0%ra; last by kat.
    move=> {}e1 {}e2 /=; split=> //.
    rewrite /r1 /r2 /hrel_dot=> [[e3]].        
    move=> /andP[] ? /eqP-> /andP[+ _].
    move: esSub=> /fsubsetP /[apply]; rewrite /lfsp_fresh.
    by move: (fresh_seq_nmem (lfsp_eventset p))=> /negP.
  ka.    
Qed.  

Lemma add_event_irrefl : supp_closed p -> 
  irreflexive (fin_ica p) -> irreflexive (fin_ica (lfspre_add_event l es p)).
Proof. 
  move=> supcl irr.  
  apply/irreflexive_mono.
  - exact/fin_ica_mono.
  move=> /=; case=> e /=. 
  rewrite add_event_eventsetE !add_event_fs_icaE // /lfsp_fresh !inE. 
  move: (fresh_seq_nmem (lfsp_eventset p))=> /negP nFr.
  move=> eIn; apply/orP=> [[|]].
  - move=> /andP[] /[swap] /eqP ->.
    by move: esSub=> /fsubsetP /[apply].
  by move: (fs_ica_irrefl supcl irr)=> ->.
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
    move: (fresh_seq_nmem (lfsp_eventset p))=> /negP nFr.
    move=> /(fs_ca_closed supcl acyc)=> /orP[|].     
    + move: in1=> /[swap] /eqP<-. 
      by move=> /lfsp_dw_clos_subs.
    by move=> /andP[].    
  - move=> /[swap] /andP[in2 /eqP ->].  
    move: (fresh_seq_nmem (lfsp_eventset p))=> /negP nFr.
    move=> /(fs_ca_closed supcl acyc)=> /orP[|].     
    + move: in2=> /[swap] /eqP<-. 
      by move=> /lfsp_dw_clos_subs.
    by move=> /andP[].    
   by move=> ??; apply/val_inj/(fs_ca_antisym acyc)/andP.
Qed.

Lemma add_event_freshE :
  lfsp_fresh (lfspre_add_event l es p) = fresh (lfsp_fresh p).
Proof. 
  rewrite /lfsp_fresh add_event_eventsetE fresh_seq_add.
  rewrite /lfsp_fresh max_l //.
  exact/ltW/fresh_lt.
Qed. 

Lemma add_event_ca_freshE e : supp_closed p -> acyclic (fin_ica p) ->
  fs_ca (lfspre_add_event l es p) e (lfsp_fresh p) = 
    (e == lfsp_fresh p) || (e \in lfsp_dw_clos p es).
Proof.
  move=> supcl acyc; rewrite add_event_fs_caE ?eqxx ?andbT=> //. 
  suff->: fs_ca p e (lfsp_fresh p) = (e == lfsp_fresh p) by rewrite orbC.
  apply/idP/idP=> [|/eqP->]; last exact/fs_ca_refl.
  move=> /(fs_ca_closed supcl acyc)=> /orP[|] //. 
  move: (fresh_seq_nmem (lfsp_eventset p))=> /negPf->. 
  by rewrite andbF.
Qed.

End Theory.
End Theory.  

End AddEvent.


Module Export lFsPosetLTS.

Module Export Def.
Section Def.  
Context (E : identType) (L : botType).
Implicit Types (l : L) (es : {fset E}).
Implicit Types (p : lfsposet E L).

Definition lfsp_add_event l es p : lfsposet E L :=
  let e := lfsp_fresh p in
  let q := lfspre_add_event l es p in
  match (l != bot) && (es `<=` (lfsp_eventset p)) =P true with
  | ReflectF _  => lFsPoset.empty E L
  | ReflectT pf => mklFsPoset
    (let: conj lD esSub := andP pf in
    let supcl := add_event_supp_closed lD esSub (lfsp_supp_closed p) in
    let acyc  := add_event_acyclic lD esSub 
                   (lfsp_supp_closed p) 
                   (lfsp_acyclic p) 
    in
    (introT andP (conj supcl acyc)))
  end.

End Def.
End Def.

(* TODO: there is a lot of copypaste from lFsPrePosetLTS ... *)
Module LTS.
Section LTS.
Context (E : identType) (L : botType).
Implicit Types (l : L) (es : {fset E}).
Implicit Types (p : lfsposet E L).

Definition ltrans l p q := 
  (l != bot) &&
  [exists es : fpowerset (lfsp_eventset p),
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
  have inPw: (fset0 \in fpowerset (lfsp_eventset p)).
  - rewrite fpowersetE; exact/fsub0set.
  pose es : fpowerset (lfsp_eventset p) := Sub fset0 inPw.
  by exists es.
Qed.
  
Definition mixin := 
  let S := lfsposet E L in
  @LTS.LTS.Mixin S L _ _ _ enabledP. 
Definition ltsType := 
  Eval hnf in let S := lfsposet E L in (LTSType S L mixin).

End LTS.

Arguments ltsType E L : clear implicits.

Module Export Exports.
Canonical ltsType.
End Exports.

End LTS.

Export LTS.Exports.

Module Export Theory.
Section Theory.  
Context (E : identType) (L : botType).
Implicit Types (l : L) (es : {fset E}).
Implicit Types (p q : lfsposet E L).
Implicit Types (tr : trace (LTS.ltsType E L)).

Import lPoset.Syntax.
Local Open Scope lts_scope.

(* TODO: remove hints? *)
Hint Resolve lfsp_supp_closed lfsp_acyclic : core.

Lemma lfsp_add_eventE l es p : l != bot -> (es `<=` lfsp_eventset p) ->
  (* --- *)
  ((lfsp_eventset (lfsp_add_event l es p) =  lfsp_fresh p |` lfsp_eventset p)   *
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
  (lfsp_size (lfsp_add_event l es p) = (lfsp_size p).+1)                        *
  (* --- *)
  (lfsp_fresh (lfsp_add_event l es p) = fresh (lfsp_fresh p)).
Proof.
  rewrite ?/lfsp_add_event; (do ? case: eqP=> //=)=> /eqP labD *.
  rewrite add_event_eventsetE //; do ? split=> //>;
  rewrite (add_event_fs_labE,
           add_event_fs_rcovE,
           add_event_fs_icaE,
           add_event_fs_caE,
           add_event_fs_sizeE,
           add_event_freshE)
    //; by case: (p)=> /=> /and3P[] //.
Qed.

Lemma add_event_ca_freshE l es p e : l != bot -> (es `<=` lfsp_eventset p) ->
  fs_ca (lfsp_add_event l es p) e (lfsp_fresh p) = 
    (e == lfsp_fresh p) || (e \in lfsp_dw_clos p es).
Proof.
  rewrite ?/lfsp_add_event; case: eqP=> //=; last first. 
  - by move=> /negP; rewrite negb_and=> /orP[|] /negP.  
  by move=> /andP[_ _] ??; rewrite add_event_ca_freshE.
Qed.

Lemma lfsp_ltransP l p q :
  reflect (l != bot /\ exists2 es, 
             es `<=` lfsp_eventset p & 
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

Lemma lfsp_trace_labels_defined tr : 
  bot \notin labels tr.
Proof. 
  case: tr=> /= ? /andP[/allP /= i ?].
  apply/mapP=>-[/= [> /i + ?]]. 
  case/lfsp_ltransP=> /eqP + ?; exact.
Qed.

Lemma lfsp_ltrans_iso p q l es : 
  l != bot -> es `<=` lfsp_eventset p -> iso_eqv q p -> 
    exists2 es', es' `<=` lfsp_eventset q &
      iso_eqv (lfsp_add_event l es' q) (lfsp_add_event l es p).
Proof.
  pose e' := fresh_seq (fresh_seq (lfsp_eventset q) |` lfsp_eventset q). 
  have ensup : e' \notin (lfsp_eventset q).
  - move: (fresh_seq_nmem (fresh_seq (lfsp_eventset q) |` lfsp_eventset q)).
    by rewrite !inE negb_or=> /andP[]. 
  have eneq : e' != lfsp_fresh q.
  - move: (fresh_seq_nmem (fresh_seq (lfsp_eventset q) |` lfsp_eventset q)).
    by rewrite !inE negb_or=> /andP[]. 
  have qnsup: lfsp_fresh q \notin lfsp_eventset q.
  - exact/fresh_seq_nmem.
  move=> lD subs /iso_eqvP[f] /[dup] [[]] labf monf bijf.
  move=> /(update_iso (lfsp_fresh p) ensup qnsup).
  pose g := upd_iso f p q e' (lfsp_fresh p) (lfsp_fresh q). 
  rewrite -/g; case=> labg homg bijg.  
  have gsubs: g @` es `<=` lfsp_eventset q.
  - apply/fsubsetP=> x /imfsetP[/=] y /(fsubsetP subs). 
    (* TODO: simplify this lemma! *)
    rewrite (lFsPoset.Hom.mono_lab_eventset _ labg).
    by move=> /[swap] ->; rewrite /g /=.
  have injg: {in lfsp_fresh p |` lfsp_eventset p &, injective g}.
  - move=> e1 e2; rewrite !in_fset1U /lfsp_fresh.
    move=> /orP[/eqP->| in1] /orP[/eqP->| in2]. 
    all: rewrite /g ?upd_iso_delta ?upd_iso_supp //.
    all: try exact/fresh_seq_nmem.
    all: try move: in2; try move: in1.
    all: rewrite ?(lFsPoset.Hom.mono_lab_eventset _ labf).
    all: move: (fresh_seq_nmem (lfsp_eventset q))=> /negP ?.
    - by move => /[swap] <-.
    - by move => /[swap] ->.
    suff: {on lfsp_eventset q &, injective f}.
    - by move=> /[apply] /[apply] /[apply].
    case bijf=> ? K ?; exact/on_can_inj/K.
  exists (g @` es)=> //; apply/iso_eqvP.
  exists g; do ? split=> // [e | e1 e2 |].
  - rewrite !fs_labE ?lfsp_add_eventE /lfsp_fresh //.
    rewrite upd_iso_delta_eq /lfsp_fresh //; last exact/fresh_seq_nmem.
    case: ifP=> // _; exact/labg.
  - rewrite !fs_caE !lfsp_add_eventE // => in1 in2.
    rewrite -fs_caE (@emb_fs_ca _ _ _ _ p q _ _ injg) //.
    rewrite upd_iso_delta_eq //; last exact/fresh_seq_nmem.
    by rewrite -(@emb_dw_clos _ _ _ g p q) //.
  case bijf=> h K K'.  
  exists [eta h with lfsp_fresh q |-> lfsp_fresh p] => e.
  all: rewrite lfsp_add_eventE // !in_fset1U /=; case: ifP=> //= [+ _|?]. 
  - rewrite ?upd_iso_delta_eq // => [/eqP|] //; exact/fresh_seq_nmem.
  - rewrite -?(lFsPoset.Hom.mono_lab_eventset _ labg)=> ein. 
    rewrite /g upd_iso_supp // ?K //.
    by rewrite -(lFsPoset.Hom.mono_lab_eventset _ labf).
  - move=> /eqP->; rewrite /g upd_iso_delta //; exact/fresh_seq_nmem.
  rewrite /g /upd_iso; case: ifP=> [?? |]; rewrite ?K' //.
  move=> /[swap] /[dup] ?; rewrite -fs_labNbot.
  by rewrite -{1}[e]K' // -fs_labE labf fs_labNbot=> ->.
Qed.

Hint Resolve lfsp_supp_closed lfsp_acyclic : core.

Lemma invariant_operational : 
  @invariant L (LTS.ltsType E L) (@operational _ _).
Proof.
  move=> p q [l /lfsp_ltransP[? [? /[dup] ? /fsubsetP sub ->]]].
  move/operationalP=> o; apply/operationalP=>> //.
  rewrite lfsp_add_eventE // => /orP[|/o]; last exact.
  case/andP=> /lfsp_dw_closP[] // ? /fs_ca_closed/orP[]//.
  - by move/eqP=>-> /sub/fresh_seq_mem/ltW ? /eqP->.
  by case/andP=> /fresh_seq_mem/ltW ??? /eqP->.
Qed.

(* TODO: invariant_conseq_num ? *)

Lemma lfsp_trace_fresh tr p:
  let emp := lFsPoset.empty E L in
  p = lst_state emp tr ->
  tr \in trace_lang emp -> lfsp_fresh p = iter (size tr) fresh \i0.
Proof.
  case: tr=> /= t it; rewrite /trace_lang /(_ \in _) /==>->.
  elim/last_ind: t it=> //= [_ _|].
  - by rewrite /lfsp_fresh lFsPrePoset.eventset_empty /fresh_seq.
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

Lemma lfsp_trace_eventset tr :
  let emp := lFsPoset.empty E L in
  let p := lst_state emp tr in
  tr \in trace_lang emp -> lfsp_eventset p = [fset e | e in nfresh \i0 (size tr)].
Proof.
  case: tr=> /= t it; rewrite /trace_lang /(_ \in _) /=.
  elim/last_ind: t it=> //= [_ _|].
  - by apply/fsetP=> ?; rewrite lFsPrePoset.eventset_empty ?inE.
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
  let emp := lFsPoset.empty E L in 
  let p := lst_state emp tr in
  tr \in trace_lang emp -> fs_lab p e = nth bot (map lbl tr) (encode e).
Proof.
  case: tr=> /= t it; rewrite /trace_lang /(_ \in _) /=.
  elim/last_ind: t it=> //= [_ _|].
  - rewrite lFsPrePoset.fs_lab_empty. 
    by case: (encode _)=> //= ?; rewrite nth_nil.
  case=> [[/=? s1 s2 ? /andP[/=/andP[st ?? /eqP]]]|].
  - move: st=> /[swap]<- /lfsp_ltransP /= [? [??->]].
    rewrite lfsp_add_eventE // /lfsp_fresh. 
    rewrite lFsPrePoset.eventset_empty fresh_seq_nil.
    rewrite lFsPrePoset.fs_lab_empty.
    case: (e =P \i1)=> [->|/eqP]; first ilia.
    by encodify; case: (encode _)=> // -//= []//= ?.
  move=> st t [l s1 s2]; rewrite fst_state_rcons /=.
  move=> IHt; rewrite -rcons_cons is_trace_rcons=> /and3P[].
  case/lfsp_ltransP=> /= ? [?? eq' /[dup] it ++ /[dup] ?].
  move=> /[swap]; rewrite /adjoint /src=> /eqP /= eq.
  move/IHt/[apply]; rewrite last_rcons /= eq.
  rewrite map_rcons /= -?rcons_cons nth_rcons /= size_map.
  rewrite eq' lfsp_add_eventE // (@lfsp_trace_fresh (Trace it)) // => ->.
  (do ? case: ifP)=> //; last (move=> *; rewrite nth_default //= size_map); ilia.
Qed.

Lemma lfsp_lang_lin tr : 
  let emp := lFsPoset.empty E L in 
  let p := lst_state emp tr in
  tr \in trace_lang emp -> labels tr \in lin p.
Proof. 
  move=> emp p inTr; rewrite /lin inE /=.
  pose q := lFsPoset.of_seq E L (map lbl tr).
  have labsD : bot \notin (map lbl tr).
  - apply/mapP=> -[[/=> /(allP (trace_steps _))/[swap]<-]].
    by case/lfsp_ltransP=> /eqP.
  rewrite -/q /=; apply/bhom_leP=> /=. 
  exists id; split=> //; last by exists id.
  repeat constructor.
  - move=> e; rewrite !fs_labE.
    rewrite lFsPoset.of_seq_valE labsD ?lFsPrePoset.of_seq_labE //=.
    by rewrite lfsp_trace_lab.
  move=> e1 e2; rewrite !fs_caE.
  rewrite lFsPoset.of_seq_valE labsD ?lFsPrePoset.of_seq_fs_caE //.
  rewrite !lFsPrePoset.of_seq_eventset //=. 
  rewrite !lfsp_trace_eventset // !in_fset /= !size_labels.
  move: (lfsp_supp_closed p)=> supcl.
  move: (lfsp_acyclic p)=> acyc.
  move=> e1In e2In Hca.
  apply/orP; right; apply/and3P; split=> //.
  apply/operationalP; last exact/Hca.
  apply/(invariant_trace_lang invariant_operational)=> //. 
  exact/lFsPrePoset.empty_operational.
Qed.

Lemma lfsp_lin_trace_lang tr : 
  let emp := lFsPoset.empty E L in 
  let p := lst_state emp tr in
  labels tr \in lin p -> tr \in trace_lang emp.
Proof.
  move=> /=; rewrite /trace_lang ?/(_ \in _) /= /lin /=.
  move/bhom_le_size; rewrite lFsPoset.of_seq_size size_map.
  rewrite lfsp_trace_labels_defined.  
  move=> sizeE; apply/eqP/esym/val_inj. 
  apply/lFsPrePoset.size0_empty => //=. 
  set f := [eta (@lfsp_size E L)]: lfsposet _ _ -> nat.
  move: (@measure_lst _ _ _ f S) sizeE=> /=; rewrite /f /= /==> -> //.
  - rewrite iter_succn; lia.
  move=> s s' l; case/lfsp_ltransP=> ? [?? ->]. 
  by rewrite lfsp_add_eventE.
Qed.

Lemma max_of_seq (ls : seq L): 
  bot \notin ls ->
  (if ls == [::] then fset0 else [fset iter (size ls).-1 fresh \i0])
  `<=` lfsp_eventset (lFsPoset.of_seq E L ls).
Proof.
  move=> labsD.
  rewrite /= lFsPoset.of_seq_valE labsD //. 
  rewrite lFsPrePoset.of_seq_eventset //.
  case: (ls)=> //= ? l'.
  rewrite fsub1set ?inE in_nfresh; ilia.
Qed.

Lemma of_seq_rcons l ls: 
  bot \notin ls ->
  l != bot ->
  lFsPoset.of_seq E L (rcons ls l) = 
  lfsp_add_event 
    l
    (if ls == [::] then fset0 else [fset iter (size ls).-1 fresh \i0])
    (lFsPoset.of_seq E L ls).
Proof.
  move=> nls nl; apply/eqP/lfspreposet_eqP.
  have labsDr: bot \notin rcons ls l. 
  - by rewrite mem_rcons ?inE negb_or eq_sym nls nl.
  have labsD: bot \notin ls. 
  - by apply/negP=> nlD; apply/(negP labsDr); rewrite mem_rcons inE nlD. 
  split=> x>; rewrite lfsp_add_eventE ?max_of_seq //.
  all: rewrite !lFsPoset.of_seq_valE !labsDr !labsD //.
  all: rewrite lFsPrePoset.of_seq_fresh //.
  - rewrite ?lFsPrePoset.of_seq_labE // nth_rcons /=.
    encodify; case: ltngtP=> // ?; rewrite nth_default //=; lia.
  have ?: bot != l by rewrite eq_sym.
  case: ifP=> [/eqP->|];
  rewrite ?lFsPrePoset.of_seq_fs_icaE ?lFsPrePoset.of_seq_eventset ?inE //=.
  - rewrite ?inE andbF; ilia.
  rewrite -size_eq0 size_rcons; ilia. 
Qed.

Lemma is_sup_fresh (X : {fset E}) : 
  is_sup (fresh_seq X |` X) (fresh_seq X).
Proof.
  apply/is_supP; split=>>; rewrite ?inE ?eqxx //.
  by move=> /orP[/eqP->|/fresh_seq_mem/ltW].
Qed.

Lemma operational_of_seq ls : 
  bot \notin ls -> operational (lFsPoset.of_seq E L ls).
Proof.
  move=> labsD; apply/operationalP=>>.
  rewrite lFsPoset.of_seq_caE labsD //.
  by case/orP=> [/eqP->|/andP[->]].
Qed.

Section BackwardStep.
Context (p : lfsposet E L) (n : nat).
Hypothesis oper : operational p.
Hypothesis fs_p : lfsp_eventset p = [fset e | e in nfresh \i0 n].
Hypothesis ne0n : n != 0%N.

Let e : E := iter n.-1 fresh \i0.

(* TODO: move to lFsPoset.Theory *)
Lemma emax : [forall y : lfsp_eventset p, ~~ fs_ica p e (val y)].
Proof.
  apply/forallP=> -[]/= f. 
  rewrite fs_p ?inE /==> ?; apply/negP.
  move/operational_scaP: oper.
  move/[swap]/(@t_step E (fs_ica p)).
  move/(fs_scaP _ _ (lfsp_supp_closed _) (lfsp_acyclic _)).
  move/[swap]/[apply]; ilia.
Qed.

(* TODO: remove hint? *)
Hint Resolve emax : core.

Lemma fresh_del : lfsp_fresh (lFsPoset.delete p e) = e.
Proof.
  pose i0x := @le0x _ E. 
  case: (n =P 1%N) fs_p emax=> [|?].
  - rewrite /e=>-> /= fsp ?; rewrite /lfsp_fresh lFsPoset.lfsp_delE // fsp.
    have: ([fset e | e in [:: \i0]] `\ \i0 =i ([::] : seq E)).
    - by move=>>; rewrite ?inE; case: (_ =P _).
    rewrite /fresh_seq nfreshS nfresh0 /= => eqm.
    under (max_set_eq i0x)=> x.
    - exact/eq_mem_map/eqm.
    done.
  rewrite /lfsp_fresh lFsPoset.lfsp_delE // fs_p.
  have: [fset e' | e' in nfresh \i0 n] `\ e =i nfresh \i0 n.-1.
  - move=>>; rewrite ?inE /=; ilia.
  rewrite /fresh_seq=> eqm eqs emax. 
  under (max_set_eq i0x)=> x.
  - exact/eq_mem_map/eqm.
  apply/fresh_seq_nfresh; lia. 
Qed.

Lemma backward_step : 
  exists q, q --[fs_lab p e]--> p.
Proof.
  exists (lFsPoset.delete p e); apply/lfsp_ltransP.
  have nb: (fs_lab p e != bot).
  - rewrite fs_labNbot fs_p ?inE /=; ilia.
  split=> //.
  have ess: (p e).2 `<=` lfsp_eventset (lFsPoset.delete p e).
  - rewrite lFsPoset.lfsp_delE //; apply/fsubsetP=> x /[dup]; rewrite in_fsetD1.
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
  let emp := lFsPoset.empty E L in 
  bot \notin ls ->
  is_hom id p (lFsPoset.of_seq E L ls) ->
  exists2 tr : trace _,
      lst_state emp tr = p & 
      labels tr = ls.
Proof.
  elim/last_ind: ls p=>/=.    
  - move=> ? _ homf; exists [trace] => //=.
    apply/esym/val_inj/lFsPrePoset.size0_empty. 
    + exact/lfsp_supp_closed.
    rewrite /lfsp_size (is_hom_id_finsuppE homf).
    rewrite lFsPoset.of_seq_valE //.
    by move: lFsPrePoset.of_seq_size; rewrite /lfsp_size=>->.
  move=> ls l IHl p nb homf.
  case: (@backward_step p (size ls).+1).
  - exact/(is_hom_operational homf)/operational_of_seq.
  - rewrite (is_hom_id_finsuppE homf) lFsPoset.of_seq_valE nb //.
    by rewrite lFsPrePoset.of_seq_eventset // size_rcons.
  - lia.
  move=> q.
  pose n := (size ls).+1.
  pose e : E := iter n.-1 fresh \i0.
  have->: fs_lab p e = l.
  - case: homf=> /(_ e); rewrite ?fs_labE /=.
    rewrite lFsPoset.of_seq_labE nb //.
    encodify; rewrite nth_rcons.
    case: ifP; first lia; by rewrite eqxx.
  move=> str; move: nb homf.
  rewrite mem_rcons ?inE negb_or=> /andP[/[1! eq_sym]??].
  rewrite of_seq_rcons // => homf.
  have?: 
    (if ls == [::] then fset0 else [fset iter (size ls).-1 fresh \i0])
    `<=` lfsp_eventset (lFsPoset.of_seq E L ls).
  - exact/max_of_seq.
  move: (str); case/lfsp_ltransP=> ?[es ?/[dup] pE->].
  move: homf=> /[dup] homf /is_hom_id_finsuppE.
  rewrite pE ?lfsp_add_eventE // => fE.
  have fqE: lfsp_fresh (lFsPoset.of_seq E L ls) = lfsp_fresh q.
  - apply/(@is_sup_uniq _ _ (lfsp_fresh q |` lfsp_eventset q)).
    + rewrite fE; exact/is_sup_fresh.
    exact/is_sup_fresh.
  have fsE: lfsp_eventset q = lfsp_eventset (lFsPoset.of_seq E L ls).
  - apply/fsetP=> x; move/fsetP/(_ x): fE; rewrite !in_fset1U fqE.
    case: (x =P _)=> //->_; by rewrite -{2}fqE ?(negbTE (fresh_seq_nmem _)).
  case: (IHl q)=> //.
  - move: homf; rewrite /is_hom /lab ?fs_labE /==> -[lf lc]; split.
    + move: lf=> /[swap] x /(_ x); rewrite pE ?lfsp_add_eventE // fqE.
      case: ifP=> // /eqP-> _.
      by rewrite ?fs_lab_bot // -?fsE /lfsp_fresh fresh_seq_nmem.
    + move: lc=> /[swap] e1 /(_ e1)/[swap] e2 /(_ e2) /[swap]in1/[swap] in2.
      have /negbTE nf: e2 != lfsp_fresh q. 
      * apply/eqP; move: in2=> /[swap]->.
        by rewrite (negbTE (fresh_seq_nmem _)).
      rewrite ?/(_ <= _) /= pE ?lfsp_add_eventE // fqE nf ?andbF /=. 
      rewrite !in_fset1U in1 in2 ?orbT; exact.
  move=> tr lstE labE.
  have it: is_trace (rcons tr (mk_step l q p)).
  - rewrite is_trace_rcons; apply/and3P; split=> //.
    + by case: (tr).
    rewrite adjoint_lastE /=; apply/eqP; by case: (val tr) lstE.
  exists (Trace it)=> /=; rewrite ?lst_state_rcons // /labels map_rcons.
  exact/congr2.
Qed.

End Theory.
End Theory.  

End lFsPosetLTS.

Module Export PomsetLTS.
(* TODO: there is a lot of copypaste from lFsPrePosetLTS ... *)
Module LTS.
Section LTS.
Context (E : identType) (L : botType).
Implicit Types (l : L) (es : {fset E}).
Implicit Types (p q : pomset E L).

Definition ltrans l (p q : lfsposet E L) := 
  (l != bot) &&
  [exists es : fpowerset (lfsp_eventset p),
    iso_eqv q (lfsp_add_event l (val es) p) 
  ]. 

Lemma pom_ltrans_repr l : 
  {mono pom : p q / ltrans l p q >-> ltrans l (repr p) (repr q)}.
Proof.
  move=>p>; case: pomP=> q /eqmodP /= eqv.
  case: pomP=> ? /eqmodP /= e1.
  apply/andP/andP=> -[/[dup]nl-> /existsP[[/= es /[! fpowersetE] s]]].
  - move: eqv=> /(lfsp_ltrans_iso _)-/(_ _ _ nl s)[es' ?? e2]. 
    split=> //; apply/existsP. 
    have ines : es' \in fpowerset (lfsp_eventset p) by rewrite fpowersetE.
    exists [`ines] => /=; apply/(iso_eqv_trans e1)/(iso_eqv_trans e2).
    by rewrite iso_eqv_sym.
  - rewrite -iso_eqv_sym in eqv.
    move: eqv=> /(lfsp_ltrans_iso _)-/(_ _ _ nl s)[es' ? e3 e2]. 
    split=> //; apply/existsP. 
    have ines : es' \in fpowerset (lfsp_eventset q) by rewrite fpowersetE.
    exists [`ines] => /=; rewrite iso_eqv_sym. 
    by apply/(iso_eqv_trans _ e1)/(iso_eqv_trans e3); rewrite iso_eqv_sym.
Qed.

Canonical ltrans_quote_mono2 l := PiMono2 (pom_ltrans_repr l).

Lemma enabledP l p :
  reflect (exists q, ltrans l (repr p) (repr q)) (l != bot).
Proof.
  apply/(iffP (LTS.enabledP _ (repr p)))=> /= -[q].
  - case/lfsp_ltransP=> ? [es ? eq]; exists (pom q).
    rewrite -[p]reprK piE; apply/andP; split=> //.
    have ines : es \in fpowerset (lfsp_eventset (repr p)) by rewrite fpowersetE.
    apply/existsP; exists [`ines]; rewrite eq; exact/iso_eqv_refl.
  case/andP=> ? /existsP[[/= es /[! fpowersetE] ??]].
  exists (lfsp_add_event l es (repr p)).
  by apply/lfsp_ltransP; split=> //; exists es.
Qed.
  
Definition mixin := 
  let S := pomset E L in
  @LTS.LTS.Mixin S L _ _ _ enabledP. 
Definition pomltsType := 
  Eval hnf in let S := pomset E L in (LTSType S L mixin).

End LTS.

Arguments pomltsType E L : clear implicits.

Module Export Exports.
Canonical pomltsType.
Canonical ltrans_quote_mono2.
End Exports.

End LTS.

Export LTS.Exports.

Module Export Theory.
Section Theory.  
Context (E : identType) (L : botType).
Implicit Types (l : L) (es : {fset E}).
Implicit Types (p q : pomset E L).
Implicit Types (tr : trace (LTS.pomltsType E L)).

Import lPoset.Syntax.
Local Open Scope lts_scope.

Export Simulation.Exports.
Import Simulation.Syntax.

Definition R : hrel (pomset E L) (lfsposet E L) := 
  iso_eqv.

Lemma ltransP l (p q : lfsposet E L) :
  reflect (l != bot /\ exists2 es, 
             es `<=` lfsp_eventset p & 
             iso_eqv q (lfsp_add_event l es p))
          (LTS.ltrans l p q).
Proof.
  rewrite /ltrans /= /LTS.ltrans.
  apply: (andPP idP). 
  apply/(equivP idP); split=> [/existsP|] /=.
  - move=> [es]; exists (val es)=> //.
    rewrite -fpowersetE; exact/(valP es). 
  move=> [es] +; rewrite -fpowersetE.
  move=> inPw ?; apply/existsP=> /=.
  by exists (Sub es inPw).
Qed.


Lemma iso_sim_class_of : Simulation.class_of 
  (iso_eqv : hrel (pomset E L) (lfsposet E L)).
Proof.
  do ? split; rewrite /ltrans /==> l s1 t1 t2 ?.
  case/lfsp_ltransP=> ? [es ? t2E].
  exists (pom t2); first by rewrite -eqquot_piE.
  have->: s1 = pom t1.
  - apply/eqP; by rewrite eqquot_piE.
  rewrite piE t2E; apply/ltransP; split=>//; by exists es.
Qed.

Definition iso_sim := Simulation.Pack iso_sim_class_of.

Lemma iso_sim_tr_class_of : Simulation.class_of 
  (iso_eqv : hrel (lfsposet E L) (pomset E L)).
Proof.
  do ? split; rewrite /ltrans /==> l s1 t1 t2.
  rewrite iso_eqv_sym -eqquot_piE=> /eqP->.
  rewrite -{1}[t2]reprK piE=> /ltransP[? [es ??]].
  exists (lfsp_add_event l es s1); first by rewrite iso_eqv_sym.
  by apply/lfsp_ltransP; split=> //; exists es.
Qed.

Definition iso_sim_tr := Simulation.Pack iso_sim_tr_class_of.

Notation of_seq := (lFsPoset.of_seq E L).

Lemma pomset_linP p (ls : seq L) :
  let emp := lFsPoset.empty E L in 
  bot \notin ls ->
    reflect 
      (exists tr : trace _,
          [/\ labels tr = ls,
              tr \in trace_lang (pom emp) &
              lst_state (pom emp) tr = p])
      (ls \in lin p).
Proof.
  move=> emp nl.
  have ise: iso_sim (pom emp) emp by rewrite /= -eqquot_piE.
  apply/(iffP idP)=> [/[dup] lsl |].
  - rewrite inE=> /bhom_factor[q eqv] /(lfsp_lin_lang nl)[tr].
    move=> /[swap]/[dup] lsE <- lE.
    have ispq: iso_sim p q by rewrite /= iso_eqv_sym.
    have tr_lang: tr \in trace_lang emp.
    - apply/lfsp_lin_trace_lang; rewrite /= in ispq.
      by rewrite (eqquot_piP _ _ ispq) piE -lE -lsE in lsl.
    case: (sim_trace ise tr_lang lE)=> tr' [??/=].
    move=> /(iso_eqv_trans)-/(_ _ eqv).
    rewrite -eqquot_eqE=> /eqP.
    by exists tr'.
  case=> tr [<-] tl lt.
  have ise': iso_sim_tr emp (pom emp) by rewrite /= iso_eqv_sym in ise.
  have isp: iso_sim_tr (repr p) p by rewrite /= iso_eqv_refl.
  case: (sim_trace ise' tl lt)=> tr' [<- /lfsp_lang_lin /[swap] /=].
  rewrite iso_eqv_sym -eqquot_piE=> /eqP->.
  by rewrite -pom_lin_mono.
Qed.

End Theory.
End Theory.

End PomsetLTS.
