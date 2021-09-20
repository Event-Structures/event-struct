From RelationAlgebra Require Import lattice monoid rel.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import seq tuple path.
From eventstruct Require Import utils relalg.

(******************************************************************************)
(* This file provides a theory of labelled transition systems (LTS),          *)
(* traces and languages of LTS, and simulation relations between LTS.         *)
(*                                                                            *)
(*         ltsType L == a type of states of labelled transition system with   *)
(*                      labels from L. Currently the library supports only    *)
(*                      discrete states, i.e. the type of states should have  *)
(*                      decidable equality.                                   *)
(*             trans == transition relation of type L -> S -> S -> bool.      *)
(*    s1 --[l]--> s2 == there exists a transition from s1 to s2 labelled by l.*)
(*         s1 --> s2 == there exists a transition from s1 to s2.              *)
(*        s1 -->? s2 == s1 is equal to s2 or s1 --> s2.                       *)
(*        s1 -->+ s2 == there exists a non-empty sequence of steps            *)
(*                      from s1 to s2.                                        *)
(*        s1 -->* s2 == there exists a possibly empty sequence of steps       *)
(*                      from s1 to s2.                                        *)
(*            step S == a type of steps of the LTS.                           *)
(*                   := { (lbl, src, dst) | src --[lbl]--> dst }.             *)
(*           trace S == a type of traces of the LTS, that is finite sequences *)
(*                      of steps performed by the transition system.          *)
(*                   := { tr : seq (step S) | dst st[i] == src st[i+1] }.     *)
(*     [trace of ts] == a trace whose underlying sequence (value) is ts.      *)
(*                      Coq must be able to infer a proof that ts satisfies   *)
(*                      trace property (i.e the ends of steps should match).  *)
(*           [trace] == empty trace.                                          *)
(*         labels tr == a sequence of labels of tr.                           *)
(*       states s tr == a sequence of states of tr or [:: s] is tr is empty.  *)
(*    fst_state s tr == the first state of of tr or s is tr is empty.         *)
(*    lst_state s tr == the last state of of tr or s is tr is empty.          *)
(*   adjoint tr1 tr2 == a relation asserting that two traces are adjoint,     *)
(*                      meaning that the last state of tr1 is equal to        *)
(*                      the first state of tr2.                               *)
(*      trace_lang s == a (decidable) predicate defining a trace language     *)
(*                      (a set of traces) of the LTS at the state s,          *)
(*                      i.e. valid traces starting at the state s.            *)
(*        lts_lang s == a predicate defining a language (a set of label       *)
(*                      sequences) of the LTS at the state s.                 *)
(*                                                                            *)
(* We also develop a theory of simulations between transition systems.        *)
(*           sim S T == a type of simulation relations between S and T.       *)
(*         bisim S T == a type of bisimulation relations between S and T.     *)
(* The following important lemmas about simulations are available.            *)
(*    sim_lang R s t == if R is simulation and R s t holds then               *)
(*                      lts_lang s ≦ lts_lang t.                              *)
(*    sim_lang R s t == if R is simulation and R s t holds then               *)
(*                      lts_lang s ≡ lts_lang t.                              *)
(*                                                                            *)
(* The following notations can be used by importing corresponding module:     *)
(* Import Mod.Syntax for Mod in {Simulation, Bisimulation}.                   *)
(*                  S ~>~ T == simulation.                                    *)
(*                  S ~=~ T == bisimulation.                                  *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* TODO: move to more appropriate place *)
Notation lang L := (seq L -> Prop).

Declare Scope lts_scope.
Delimit Scope lts_scope with lts.

Local Open Scope lts_scope.

Reserved Notation "s1 '--[' l ']-->' s2" (at level 22, no associativity).
Reserved Notation "s1 '-->' s2" (at level 55, right associativity).
Reserved Notation "s1 '-->?' s2" (at level 55, right associativity).
Reserved Notation "s1 '-->+' s2" (at level 22, right associativity).
Reserved Notation "s1 '-->*' s2" (at level 22, right associativity).

Module Export LTS.

Section ExLab.
Context {S L : Type}.

(* TODO: remove copypaste from `rewriting_system.v` *)
Definition exlab {S L : Type} (tr : L -> hrel S S) : hrel S S := 
  fun s1 s2 => exists l, tr l s1 s2.

End ExLab.

Module LTS.
Section ClassDef. 

Record mixin_of (S0 : Type) (L : Type)
                (sb : Equality.class_of S0)
                (S := Equality.Pack sb) := Mixin {
  trans : L -> rel S;
}.

Set Primitive Projections.
Record class_of (S : Type) (L : Type) := Class {
  base  : Countable.class_of S;
  mixin : mixin_of L base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Countable.class_of.

Structure type (L : Type) := Pack { sort; _ : class_of sort L }.

Local Coercion sort : type >-> Sortclass.

Variables (S : Type) (L : Type) (cT : type L).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') L in c.
Definition clone c of phant_id class c := @Pack S c.

Definition pack :=
  fun bS b & phant_id (@Countable.class bS) b =>
  fun m => Pack (@Class S L b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition countType := @Countable.Pack cT class.
End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Countable.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
End Exports.

End LTS.

Export LTS.Exports.

Notation ltsType := LTS.type.
Notation LTSType S L m := (@LTS.pack S L _ _ id m).

Section Def.
Context {L : Type} (S : ltsType L).

Definition trans : L -> rel S := LTS.trans (LTS.class S).

End Def.

Notation "s1 '--[' l ']-->' s2" := (trans l s1 s2) : lts_scope.
Notation "s1 '-->' s2"  := (exlab trans)   : lts_scope.
Notation "s1 '-->?' s2" := (exlab trans)^? : lts_scope.
Notation "s1 '-->+' s2" := (exlab trans)^+ : lts_scope. 
Notation "s1 '-->*' s2" := (exlab trans)^* : lts_scope.

End LTS.

(* Context {L : Type} {S : ltsType L}. *)
(* Variable (l : L) (s1 s2 : S). *)
(* Check (s1 --[l]--> s2). *)

Module Export Step. 

Section Def.
Context {L : Type} (S : ltsType L).

Record stepTuple : Type := mk_step {
  lbl : L; src : S; dst : S;  
}.

Definition is_step : pred stepTuple := 
  fun s => (src s) --[lbl s]--> (dst s).

Structure step : Type := Step {step_val :> stepTuple; _ : is_step step_val}.

Canonical step_subType := Eval hnf in [subType for step_val].

(* TODO: better name? *)
Definition lnk : rel step := 
  fun s t => dst s == src t. 
End Def.

Prenex Implicits lbl src dst is_step lnk.

Section Prod.
Context {L : Type} (S : ltsType L).

Definition prod_of_step : stepTuple S -> L * S * S := 
  fun s => (lbl s, src s, dst s).

Definition step_of_prod : L * S * S -> option (step S) := 
  fun '(lbl, src, dst) => insub (mk_step lbl src dst).

Lemma prod_of_step_inj : injective prod_of_step.
Proof. 
  rewrite /prod_of_step; move=> x y /= []. 
  by case x; case y=> /= ?????? -> -> ->. 
Qed.

Lemma prod_of_stepK : 
  pcancel (prod_of_step : step S -> L * S * S) step_of_prod.
Proof. 
  move=> st /=; rewrite insubT=> /=.
  - by move: (valP st); rewrite /is_step.
  move=> H /=; congr Some; apply/val_inj=> /=. 
  by move: H=> _; case: st=> [[]] /=.  
Qed.

End Prod.

Section EQ. 
Context {L : eqType} (S : ltsType L).

Definition stepTuple_eqMixin := InjEqMixin (@prod_of_step_inj L S).
Canonical stepTuple_eqType := 
  Eval hnf in EqType (stepTuple S) stepTuple_eqMixin.

Definition step_eqMixin := Eval hnf in [eqMixin of step S by <:].
Canonical step_eqType := Eval hnf in EqType (step S) step_eqMixin.

(* Variables (st1 st2 : step S). *)
(* Check (st1 == st2). *)

End EQ.

Section Count. 
Context {L : countType} (S : ltsType L).

Definition step_choiceMixin := PcanChoiceMixin (@prod_of_stepK L S).
Canonical step_choiceType := 
  Eval hnf in ChoiceType (step S) step_choiceMixin.

Definition step_countMixin := PcanCountMixin (@prod_of_stepK L S).
Canonical step_countType := 
  Eval hnf in CountType (step S) step_countMixin.

End Count.

End Step.


Module Export Trace. 

Notation trace_seq S := (seq (step S)).

Section Def. 
Context {L : eqType} (S : ltsType L).

Definition is_trace : pred (trace_seq S) := 
  fun s => sorted lnk s.

Structure trace : Type := Trace { 
  trace_val :> trace_seq S; 
  _         :  is_trace trace_val;
}.

Canonical trace_subType := Eval hnf in [subType for trace_val].

Implicit Types (ts : trace_seq S) (tr : trace).

Definition labels : trace_seq S -> seq L := map (lbl : step S -> L). 

Definition states : S -> trace_seq S -> seq S := 
  fun s ts => 
    match ts with 
    | [::]    => [:: s]
    | st :: _ => src st :: map (dst : step S -> S) ts
    end. 

Definition fst_state : S -> trace_seq S -> S := 
  fun s ts => if ts is st :: ts then src st else s.

Definition lst_state : S -> trace_seq S -> S := 
  fun s ts => if ts is st :: ts then dst (last st ts) else s. 

Definition nth_state : S -> trace_seq S -> nat -> S := 
  fun s ts n => if ts is st :: ts then src (nth st ts n) else s. 

Definition trace_lang : S -> pred trace := 
  fun s tr => s == fst_state s tr.

(* TODO: this is actually a fmap on (A -> Prop) functor. *)
Definition lts_lang : S -> lang L := 
  fun s w => exists tr, (w == labels tr) && (trace_lang s tr).

(* TODO: better name? *)
Definition adjoint : rel (trace_seq S) := 
  fun ts1 ts2 => 
    match ts2 with 
    | [::]    => true
    | st :: _ => lst_state (src st) ts1 == src st
    end.

Definition mk_trace tr mkTr : trace :=
  mkTr (let: Trace _ trP := tr return is_trace tr in trP).

End Def. 

Arguments adjoint : simpl never.

Section Seq.
Context {L : eqType} (S : ltsType L).
Implicit Types (st : step S) (s : trace_seq S) (tr : trace S).

Lemma nil_traceP : is_trace ([::] : seq (step S)).
Proof. done. Qed.
Canonical nil_trace := Trace nil_traceP.

End Seq.

Notation "[ 'trace' 'of' tr ]" := (mk_trace (fun trP => @Trace _ _ tr trP))
  (at level 0, format "[ 'trace'  'of'  tr ]") : form_scope.

Notation "[ 'trace' ]" := [trace of [::]]
  (at level 0, format "[ 'trace' ]") : form_scope.

Section EQ.
Context {L : eqType} (S : ltsType L).

Definition trace_eqMixin := Eval hnf in [eqMixin of trace S by <:].
Canonical trace_eqType := Eval hnf in EqType (trace S) trace_eqMixin.

End EQ.

Section Count. 
Context {L : countType} (S : ltsType L).

Definition trace_choiceMixin := Eval hnf in [choiceMixin of trace S by <:].
Canonical trace_choiceType := Eval hnf in ChoiceType (trace S) trace_choiceMixin.

Definition trace_countMixin := Eval hnf in [countMixin of trace S by <:].
Canonical trace_counType := Eval hnf in CountType (trace S) trace_countMixin.

End Count.

Section Theory. 
Context {L : eqType} (S : ltsType L).
Implicit Types (s : S) (st : step S) (ts : trace_seq S) (tr : trace S).

Lemma trace_lnk tr : sorted lnk tr.
Proof. by case: tr. Qed.

Lemma fst_state_src st ts : 
  fst_state (src st) ts = src (head st ts).
Proof. by case ts. Qed.

Lemma fst_state_rcons s ts st :
  fst_state s (rcons ts st) = src (head st ts).
Proof. by case: ts. Qed.

Lemma fst_stateNnil s s' ts : ts <> [::] ->
  fst_state s' ts = fst_state s ts.
Proof. by case: ts. Qed.

Lemma lst_state_dst ts st : 
  lst_state (dst st) ts = dst (last st ts).
Proof. by case ts. Qed.

Lemma lst_state_rcons s ts st :
  lst_state s (rcons ts st) = dst st.
Proof. 
  rewrite /lst_state headI behead_rcons.
  by case: ts=> [|??] //=; rewrite last_rcons.
Qed.

Lemma lst_stateNnil s s' ts : ts <> [::] ->
  lst_state s' ts = lst_state s ts.
Proof. by case: ts=> [|??] //; rewrite !lst_stateE. Qed. 

Lemma adjoint0s ts :
  adjoint [::] ts.
Proof. by rewrite /adjoint; case: ts=> [|??] //=. Qed.

Lemma adjoints0 ts :
  adjoint ts [::].
Proof. by rewrite /adjoint. Qed.    

Lemma adjoint_cons st ts1 ts2 :
  adjoint ts1 (st :: ts2) = adjoint ts1 [:: st]. 
Proof. by rewrite /adjoint; case: ts2=> [|??] //=. Qed.

Lemma adjoint_rcons st ts1 ts2 :
  adjoint (rcons ts1 st) ts2 = adjoint [:: st] ts2. 
Proof. 
  rewrite /adjoint; case: ts2=> [|??] //=. 
  by rewrite lst_state_rcons.
Qed.

Lemma adjoint_lnk st1 st2 :
  adjoint [:: st1] [:: st2] = lnk st1 st2.
Proof. done. Qed.

Lemma adjoint_firstE st ts : 
  adjoint [:: st] ts = (dst st == fst_state (dst st) ts).
Proof. by case: ts=> //=; rewrite /adjoint eq_refl. Qed.

Lemma adjoint_lastE ts st : 
  adjoint ts [:: st] = (lst_state (src st) ts == src st).
Proof. done. Qed.

Lemma is_trace_cons st ts : 
  is_trace (st :: ts) = [&& is_trace ts & adjoint [:: st] ts].
Proof. 
  rewrite /is_trace /adjoint /=.
  case: ts=> [|st' {}ts] //=.
  by rewrite andbC; apply/andb_id2l=> _.
Qed.

Lemma is_trace_rcons ts st : 
  is_trace (rcons ts st) = [&& is_trace ts & adjoint ts [:: st]].
Proof.
  rewrite /is_trace /adjoint. 
  case: (lastP ts)=> [|{}ts st'] //=.
  - by rewrite eq_refl.
  rewrite lst_state_rcons (sorted_rcons st). 
  by rewrite /nilp /lnk size_rcons last_rcons /=.
Qed.

Lemma size_labels ts : 
  size (labels ts) = size ts.
Proof. by rewrite /labels size_map. Qed.

Lemma labels_rcons ts st : 
  labels (rcons ts st) = rcons (labels ts) (lbl st).
Proof. by rewrite /labels map_rcons. Qed.

Lemma labels_cat ts1 ts2 : 
  labels (ts1 ++ ts2) = labels ts1 ++ labels ts2.
Proof. by rewrite /labels map_cat. Qed.

Lemma size_states s ts : size (states s ts) == (size ts).+1.
Proof. by rewrite /states; case: ts=> [|??] //=; rewrite size_map. Qed.
                         
Lemma states_rcons s ts st : s = fst_state (src st) ts -> 
  states s (rcons ts st) = rcons (states s ts) (dst st).
Proof. by case: ts=> [->|??] //=; rewrite map_rcons. Qed.

Lemma states_cat s ts1 ts2 : s = fst_state s ts2 -> 
  states s (ts1 ++ ts2) = states s ts1 ++ behead (states s ts2).
Proof. by rewrite /states map_cat; case: ts1; case: ts2=> //= ?? ->. Qed.

Lemma trace_lang0 s : 
  trace_lang s [trace].
Proof. by rewrite /trace_lang. Qed. 

Lemma lts_lang_labels s tr : 
  trace_lang s tr -> lts_lang s (labels tr).
Proof. move=> ?; exists tr; exact/andP. Qed.

End Theory.

Section Carry.
Context {L : countType} (S : ltsType L) (T : ltsType L).
Variables (s : S) (t : T) (tr : trace T).

Hypothesis (Htr : trace_lang t tr).
Hypothesis (Hlg : lts_lang t ≦ lts_lang s).

Definition carry_traceP : lts_lang s (labels tr) := 
  Hlg (lts_lang_labels Htr).

Definition carry_trace : trace S := xchoose carry_traceP.

Lemma labels_carry : 
  labels carry_trace = labels tr. 
Proof. by move: (xchooseP carry_traceP)=> /andP[/eqP<- _]. Qed.

Lemma size_carry : 
  size carry_trace = size tr. 
Proof. by rewrite -size_labels -size_labels labels_carry. Qed.
  
Lemma lts_lang_carry : 
  lts_lang s (labels carry_trace). 
Proof. 
  exists carry_trace; rewrite /carry_trace; apply/andP; split=> //. 
  by move: (xchooseP carry_traceP)=> /andP[_].
Qed.

End Carry.

Section Carry0.
Context {L : countType} (S : ltsType L) (T : ltsType L).
Variables (s : S) (t : T).

Hypothesis (Hlg : lts_lang t ≦ lts_lang s).

Lemma carry_trace0 : carry_trace (trace_lang0 t) Hlg = [trace].
Proof. 
  move: (xchooseP (carry_traceP (trace_lang0 t) Hlg)). 
  move=> /andP[/eqP Hl _]; apply/val_inj/nilP=> /=. 
  by rewrite /nilp size_carry. 
Qed.

End Carry0. 

End Trace.


Module Export Simulation.

Module Simulation.
Section ClassDef. 

(* TODO: simulation between lts labelled by different labels? *)
Context {L : Type} (S T : ltsType L).
Implicit Types (R : hrel S T).

Record mixin_of R := Mixin {
  _ : forall (l : L) (s1 : S) (t1 t2 : T), 
        R s1 t1 -> t1 --[l]--> t2 -> exists s2, 
        R s2 t2 /\ s1 --[l]--> s2;  
}.

Set Primitive Projections.
Record class_of R := Class {
  mixin : mixin_of R;
}.
Unset Primitive Projections.

Structure type := Pack { apply : S -> T -> Prop ; _ : class_of apply }.

Local Coercion apply : type >-> Funclass.

Variables (cT : type).

Definition class := let: Pack _ c as cT' := cT return class_of (apply cT') in c.
Definition clone f c of phant_id class c := @Pack f c.

(* Definition pack := *)
(*   fun bE b & phant_id (@Order.POrder.class tt bE) b => *)
(*   fun m => Pack (@Class E L b m). *)

End ClassDef.

Module Export Exports.
Coercion mixin : class_of >-> mixin_of.
Coercion apply : type >-> Funclass.
End Exports.

Module Syntax. 
Notation "S ~>~ T" := (type S T) (at level 50) : lts_scope.
End Syntax. 

End Simulation.

Export Simulation.Exports.
Import Simulation.Syntax.

Notation sim := Simulation.type.

Section Theory.
Context {L : countType} {S T : ltsType L}.
Implicit Types (R : S ~>~ T).
Implicit Types (s : S) (t : T).

Lemma sim_step R l s1 t1 t2 :
  R s1 t1 -> (t1 --[l]--> t2) -> exists s2, R s2 t2 /\ (s1 --[l]--> s2).
Proof. case: R=> ? [[H]] /=; exact/H. Qed.

Lemma sim_lang R s t : 
  R s t -> lts_lang t ≦ lts_lang s.
Proof. 
  move=> HR w [[tr Htr]] /andP[] /eqP-> /=; clear w.
  rewrite /lts_lang /trace_lang /= => /eqP Hh. 
  suff: (exists (tr' : trace S), 
           [/\ R (lst_state s tr') (lst_state t tr), 
               labels tr == labels tr' 
             & s == fst_state s tr'
           ]).
  - move=> [tr' []] => ???; exists tr'; exact/andP. 
  move: Htr Hh; elim/last_ind: tr=> [|{}tr st IH] /=.
  - by exists [trace] => /=.
  rewrite is_trace_rcons=> /andP[Htr Hj].
  rewrite fst_state_rcons -fst_state_src. 
  case: (nilp tr)/nilP=> [->|Hnil] /=. 
  - move: (valP st); rewrite /is_step=> /[swap] <- => Hs. 
    move: (sim_step HR Hs)=> [s' [HR' Hs']].
    (* TODO: introduce a nicer way to construct steps 
     *   (using canonical structures and phantom types?) 
     *)
    pose st_' := mk_step (lbl st) s s'. 
    have Hst' : is_step st_' by done. 
    pose st'  := Step Hst'.     
    have Htr' : is_trace [:: st']. 
    - by rewrite is_trace_cons //=; apply/andP.
    by exists (Trace Htr')=> //=. 
  rewrite (fst_stateNnil t) // => Ht.
  move: (IH Htr Ht); clear IH. 
  move=> [tr' []] /[swap].
  rewrite !labels_rcons.    
  move: Hj; rewrite adjoint_lastE=> /eqP. 
  rewrite (lst_stateNnil t (src st))=> // ->. 
  move: (valP st); rewrite /is_step=> Hs /eqP Hlbl HRl.
  move: (sim_step HRl Hs)=> [s' []].
  move=> HR' Hs' /eqP Hfst.
  have: ~~ nilp tr'.
  - rewrite /nilp -size_labels -Hlbl size_labels. 
    by move: Hnil=> /nilP.
  move=> /nilP Hnil'.
  pose st_' := mk_step (lbl st) (lst_state s tr') s'.
  have Hst' : is_step st_' by done.
  pose st'  := Step Hst'.
  have Htr' : is_trace (rcons tr' st'). 
  - rewrite is_trace_rcons; apply /andP; split=> //.
    - exact/(valP tr').
    rewrite adjoint_lastE /=.
    by apply/eqP/lst_stateNnil.
  exists (Trace Htr')=> /=; split.
  - by rewrite !lst_state_rcons /=.
  - by rewrite labels_rcons Hlbl.
  rewrite fst_state_rcons Hfst -fst_state_src. 
  by apply/eqP/fst_stateNnil.
Qed.

(* Definition helper s t (tr : trace T)  *)
(*                       (Htr : trace_lang t tr)  *)
(*                       (Hlg : lts_lang t ≦ lts_lang s) : *)
(*   { tr' : trace S | (labels tr == labels tr') && trace_lang s tr' }. *)
(* Proof.  *)
(*   pose Htr' := (Hlg (labels tr) (lts_lang_labels Htr)). *)
(*   pose tr'  := xchoose Htr'. *)
(*   refine (@exist _ _ tr' (xchooseP Htr')). *)
(* Defined. *)

Lemma lang_sim s t : 
  lts_lang t ≦ lts_lang s -> exists (R : S ~>~ T), R s t.
Proof. 
  move=> Hlg.
  unshelve eexists; first (unshelve eexists).
  - move=> s' t'.
    refine (exists (tr : { tr : trace T | trace_lang t tr}), _).
    move: tr=> [tr Htr].
    pose tr' := carry_trace Htr Hlg.
    refine (exists n, (t' == nth_state t tr n) && (s' == nth_state s (val tr') n)).    
  repeat constructor=> /=. 
  move=> l s1 t1 t2 [[tr1 Htr1]] /=. 
  move=> [n] /andP[] /eqP Ht1 /eqP Hs1 Hst.
  
  have tr2 : trace T.
  - admit.
  have Hst' : is_step (mk_step l t1 t2).
  - done.
  have HtrE : tr2 = rcons (take n tr1) (Step Hst') :> trace_seq T.
  - admit.
  have Htr2 : trace_lang t tr2. 
  - admit.
  pose tr2' := carry_trace Htr2 Hlg.
  (* move: (xchooseP (Hlg (labels tr2) (lts_lang_labels Htr2))). *)
  (* rewrite <- HH' in *. *)
  (* move=> /andP[] /eqP Hl' Htr2'.  *)

  exists (nth_state s tr2' n.+1).
  eexists; last first.
  - admit.
  unshelve eexists. 
  - by exists tr2. 
  move=> /=; exists n.+1.
  apply/andP; split=> //.
  admit.
  
  move=> /=. unshelve eexists.
  - exact/(@exist _ _ [trace] (trace_lang0 t)).
  move=> /=; exists 0%nat. 
  apply/andP; split=> //.
  by rewrite carry_trace0.    

Admitted.

End Theory.

End Simulation. 


Module Export Bisimulation.

Module Bisimulation.
Section ClassDef. 

(* TODO: simulation between lts labelled by different labels? *)
Context {L : Type} (S T : ltsType L).
Implicit Types (R : hrel S T).

Set Primitive Projections.
Record class_of R := Class {
  base  : Simulation.class_of R ; 
  mixin : Simulation.mixin_of R°;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Simulation.class_of.

Structure type := Pack { apply : S -> T -> Prop ; _ : class_of apply }.

Local Coercion apply : type >-> Funclass.

Variables (cT : type).

Definition class := let: Pack _ c as cT' := cT return class_of (apply cT') in c.
Definition clone f c of phant_id class c := @Pack f c.

(* Definition pack := *)
(*   fun bE b & phant_id (@Order.POrder.class tt bE) b => *)
(*   fun m => Pack (@Class E L b m). *)

Definition simType := Simulation.Pack class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Simulation.Simulation.class_of.
(* Coercion mixin : class_of >-> mixin_of. *)
Coercion apply : type >-> Funclass.
Coercion simType : type >-> Simulation.type.
Canonical simType.
End Exports.

Module Import Syntax. 
Notation "S ~=~ T" := (type S T) (at level 50) : lts_scope.
End Syntax. 

End Bisimulation.

Export Bisimulation.Exports.
Import Bisimulation.Syntax.

Notation bisim := Bisimulation.type.

Section Build.
Context {L : Type}.
Implicit Types (S T : ltsType L).

Lemma inv_class S T (R : S ~=~ T) : Bisimulation.class_of (R : hrel S T)°.
Proof. by case: R=> [? [[] []]] /=. Qed.

Definition inv S T : (S ~=~ T) -> (T ~=~ S) := 
  fun R => Bisimulation.Pack (inv_class R). 

End Build.

Section Theory.
Context {L : eqType} {S T : ltsType L}.
Implicit Types (R : S ~=~ T).

Lemma sim_step_cnv R l s1 s2 t1 :
  R s1 t1 -> (s1 --[l]--> s2) -> exists t2, R s2 t2 /\ (t1 --[l]--> t2).
Proof. case: R=> ? [[? [H]]] /=; exact/H. Qed.

Lemma bisim_lang R s t : 
  R s t -> lts_lang t ≡ lts_lang s.
Proof. 
  move=> HR; apply/weq_spec; split. 
  - exact/(sim_lang HR).
  by apply/(@sim_lang _ _ _ (inv R))=> /=.
Qed.

End Theory.

End Bisimulation. 
