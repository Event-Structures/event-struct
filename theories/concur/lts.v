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
(*         step_of H == given a proof of step property H : s --[l]--> s'      *)
(*                      constructs a step { (l, s, s') | s --[l]--> s' }.     *)
(*           trace S == a type of traces of the LTS, that is finite sequences *)
(*                      of steps performed by the transition system.          *)
(*                   := { tr : seq (step S) | dst tr[i] == src tr[i+1] }.     *)
(*     [trace of ts] == a trace whose underlying sequence (value) is ts.      *)
(*                      Coq must be able to infer a proof that ts satisfies   *)
(*                      trace property (i.e the ends of steps should match).  *)
(*           [trace] == empty trace.                                          *)
(*       tr1 <+> tr2 == concatenation of traces tr1 ++ tr2 if tr1 and tr2     *)
(*                      are adjoint, empty trace otherwise.                   *)
(*          st <+ tr == cons of step st and trace tr if they are are adjoint, *)
(*                      empty trace otherwise.                                *)
(*          tr +> st == rcons of step st and trace tr if they are are adjoint,*)
(*                      empty trace otherwise.                                *)
(*         labels tr == a sequence of labels of a trace.                      *)
(*       states s tr == a sequence of states of tr or [:: s] if tr is empty.  *)
(*    fst_state s tr == the first state of tr or s is tr is empty.            *)
(*    lst_state s tr == the last state of tr or s is tr is empty.             *)
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

Reserved Notation "s1 '--[' l ']-->' s2" (at level 55, no associativity).

Reserved Notation "s1 '-->' s2"  (at level 55, right associativity).
Reserved Notation "s1 '-->?' s2" (at level 55, right associativity).
Reserved Notation "s1 '-->+' s2" (at level 55, right associativity).
Reserved Notation "s1 '-->*' s2" (at level 55, right associativity).

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
                (sb : Countable.class_of S0)
                (S := Countable.Pack sb) := Mixin {
  trans     : L -> rel S;
  has_trans : L -> S -> bool;

  _ : forall l s, reflect (exists s', trans l s s') (has_trans l s);
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
Implicit Types (l : L) (s : S).

Definition trans : L -> rel S := LTS.trans (LTS.class S).

Definition has_trans : L -> S -> bool := LTS.has_trans (LTS.class S).

Lemma has_transP l s : 
  reflect (exists s', trans l s s') (has_trans l s).
Proof. by rewrite /trans /has_trans; move: s; case: S=> ? [? []]. Qed. 

Definition pick_trans l s : option S := 
  match @idP (has_trans l s) with 
  | ReflectT pf => 
     let exP := elimT (has_transP l s) pf in 
     Some (xchoose exP)
  | ReflectF pf => None 
  end.

End Def.

Notation "s1 '--[' l ']-->' s2" := (trans l s1 s2) : lts_scope.
Notation "s1 '-->' s2"  := (exlab trans)   : lts_scope.
Notation "s1 '-->?' s2" := (exlab trans)^? : lts_scope.
Notation "s1 '-->+' s2" := (exlab trans)^+ : lts_scope. 
Notation "s1 '-->*' s2" := (exlab trans)^* : lts_scope.

Section Theory.
Context {L : Type} (S : ltsType L).
Implicit Types (l : L) (s : S).

Lemma has_transE l s : 
  has_trans l s = pick_trans l s.
Proof. by rewrite /pick_trans; destruct idP. Qed.

Lemma pick_trans_some l s s' :
  pick_trans l s = Some s' -> s --[l]--> s'.
Proof. rewrite /pick_trans; destruct idP=> // [[<-]]; exact/xchooseP. Qed.

End Theory.

End LTS.


Module Export dLTS.

Module dLTS.
Section ClassDef. 

Record mixin_of (S0 : Type) (L : Type)
                (sb : LTS.class_of S0 L)
                (S := LTS.Pack sb) := Mixin {
  _ : forall (l : L) (s1 s2 s3 : S), 
        (s1 --[l]--> s2) -> (s1 --[l]--> s3) -> s2 = s3
}.

Set Primitive Projections.
Record class_of (S : Type) (L : Type) := Class {
  base  : LTS.class_of S L;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> LTS.class_of.

Structure type (L : Type) := Pack { sort; _ : class_of sort L }.

Local Coercion sort : type >-> Sortclass.

Variables (S : Type) (L : Type) (cT : type L).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') L in c.
Definition clone c of phant_id class c := @Pack S c.

Definition pack :=
  fun bS b & phant_id (@LTS.class bS) b =>
  fun m => Pack (@Class S L b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition countType := @Countable.Pack cT class.
Definition ltsType := @LTS.Pack L cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> LTS.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Coercion ltsType : type >-> LTS.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical ltsType.
End Exports.

End dLTS.

Export dLTS.Exports.

Notation dltsType := dLTS.type.
Notation dLTSType S L m := (@dLTS.pack S L _ _ id m).

Section Theory.
Context {L : Type} {S : dltsType L}.
Implicit Types (l : L) (s : S).

Lemma trans_det l s1 s2 s3 : 
  (s1 --[l]--> s2) -> (s1 --[l]--> s3) -> s2 = s3.
Proof. rewrite /trans; move: s1 s2 s3; case: S=> ? [? [H]]; exact/H. Qed.

Lemma transE l s s' : 
  (pick_trans l s == Some s') = (s --[l]--> s').
Proof. 
  apply/idP/idP=> [/eqP|]; first exact/pick_trans_some.
  rewrite /pick_trans=> Htr; apply/eqP. 
  destruct idP; last first; [|congr Some].
  - by exfalso; apply/n/has_transP; exists s'. 
  move: (xchooseP (has_transP l s i))=> Htr'.
  by apply/(trans_det Htr').
Qed.

End Theory.

End dLTS.


(* Context {L : Type} {S : ltsType L}. *)
(* Variable (l : L) (s1 s2 : S). *)
(* Check (s1 --[l]--> s2). *)

Module Export Step. 

Section Def.
Context {L : Type} (S : ltsType L).
Implicit Types (l : L) (s : S).

Record stepTuple : Type := mk_step {
  lbl : L; src : S; dst : S;  
}.

Definition is_step : pred stepTuple := 
  fun st => (src st) --[lbl st]--> (dst st).

Structure step : Type := Step {step_val :> stepTuple; _ : is_step step_val}.

Canonical step_subType := Eval hnf in [subType for step_val].

Definition step_of l s s' : (s --[l]--> s') -> step := 
  fun p => @Step (mk_step l s s') p.

Definition adj : rel stepTuple := 
  fun st st' => dst st == src st'. 

End Def.

Prenex Implicits lbl src dst is_step step_of adj.

Section Prod. 
Context {L : Type} (S : ltsType L).

Definition prod_of_step : stepTuple S -> L * S * S := 
  fun s => (lbl s, src s, dst s).

Definition step_of_prod : L * S * S -> stepTuple S := 
  fun '(lbl, src, dst) => mk_step lbl src dst.

Lemma prod_of_step_inj : injective prod_of_step.
Proof. 
  rewrite /prod_of_step; move=> x y /= []. 
  by case x; case y=> /= ?????? -> -> ->. 
Qed.

Lemma prod_of_stepK : 
  cancel prod_of_step step_of_prod.
Proof. by case. Qed.

End Prod.

Section EQ.
Context {L : eqType} (S : ltsType L).

Definition stepTuple_eqMixin := InjEqMixin (@prod_of_step_inj L S).
Canonical stepTuple_eqType := 
  Eval hnf in EqType (stepTuple S) stepTuple_eqMixin.

Definition step_eqMixin := Eval hnf in [eqMixin of step S by <:].
Canonical step_eqType := Eval hnf in EqType (step S) step_eqMixin.

End EQ.

Section Choice.
Context {L : choiceType} (S : ltsType L).

Definition stepTuple_choiceMixin := 
  CanChoiceMixin (@prod_of_stepK L S).
Canonical stepTuple_choiceType := 
  Eval hnf in ChoiceType (stepTuple S) stepTuple_choiceMixin.

Definition step_choiceMixin := 
  Eval hnf in [choiceMixin of step S by <:].
Canonical step_choiceType := 
  Eval hnf in ChoiceType (step S) step_choiceMixin.

End Choice.

Section Countable.
Context {L : countType} (S : ltsType L).

Definition stepTuple_countMixin := 
  CanCountMixin (@prod_of_stepK L S).
Canonical stepTuple_countType := 
  Eval hnf in CountType (stepTuple S) stepTuple_countMixin.

Definition step_countMixin := 
  Eval hnf in [countMixin of step S by <:].
Canonical step_countType := 
  Eval hnf in CountType (step S) step_countMixin.

Canonical step_subCountType := [subCountType of (step S)].

End Countable.

Section Theory.
Context {L : eqType} (S : ltsType L).
Implicit Types (l : L) (s : S).

Lemma step_of_val l s s' (Hst : s --[l]--> s') : 
  step_of Hst = mk_step l s s' :> stepTuple S.
Proof. done. Qed.

End Theory.

End Step.


Module Export Trace. 

Notation traceSeq S := (seq (stepTuple S)).

Section Def. 
Context {L : Type} (S : ltsType L).

Definition is_trace : pred (traceSeq S) := 
  fun ts => all is_step ts && sorted adj ts.

Structure trace : Type := Trace { 
  trace_val :> traceSeq S; 
  _         :  is_trace trace_val;
}.

Canonical trace_subType := Eval hnf in [subType for trace_val].

Implicit Types (ts : traceSeq S) (tr : trace).

Definition labels : traceSeq S -> seq L := map lbl. 

Definition states : S -> traceSeq S -> seq S := 
  fun s ts => 
    match ts with 
    | [::]    => [:: s] 
    | st :: _ => src st :: map dst ts
    end. 

Definition trace_from : S -> seq L -> traceSeq S :=
  fun s ls => 
    let fix aux s ls :=
      match ls with
      | [::]    => [::]
      | l :: ls =>
        match pick_trans l s with
        | None    => [::]
        | Some s' => mk_step l s s' :: (aux s' ls) 
        end
      end
    in aux s ls.

(* Definition trace_from : S -> seq L -> trace := *)
(*   fun s ls =>  *)
(*     let fix aux acc s ls := *)
(*       match ls with *)
(*       | [::]    => [::] *)
(*       | l :: ls => *)
(*         match pick_trans l s with *)
(*         | None    => acc *)
(*         | Some s' => aux (mk_step l s s' :: acc) s' ls  *)
(*         end *)
(*       end *)
(*     in  *)
(*     insub_trace (rev (aux [::] s ls)). *)

(* TODO: try `starts_with` and `ends_with` predicates instead? *)
Definition fst_state : S -> traceSeq S -> S := 
  fun s ts => if ts is st :: ts then src st else s.

Definition lst_state : S -> traceSeq S -> S := 
  fun s ts => if ts is st :: ts then dst (last st ts) else s. 

Definition trace_lang : S -> pred trace := 
  fun s tr => s == fst_state s tr.

(* TODO: this is actually a fmap on (A -> Prop) functor. *)
Definition lts_lang : S -> lang L := 
  fun s w => exists2 tr, trace_lang s tr & w = labels tr.

Definition adjoint : rel (traceSeq S) := 
  fun ts1 ts2 => 
    match ts2 with 
    | [::]    => true
    | st :: _ => lst_state (src st) ts1 == src st
    end.

Definition adjoin : traceSeq S -> traceSeq S -> traceSeq S :=
  fun ts1 ts2 => if adjoint ts1 ts2 then ts1 ++ ts2 else [::].

Definition mk_trace tr mkTr : trace :=
  mkTr (let: Trace _ trP := tr return is_trace tr in trP).

End Def. 

Arguments adjoint : simpl never.

Notation "[ 'trace' 'of' tr ]" := (mk_trace (fun trP => @Trace _ _ tr trP))
  (at level 0, format "[ 'trace'  'of'  tr ]") : form_scope.

Notation "[ 'trace' '::' st ]" := [trace of [:: val st]]
  (at level 0, format "[ 'trace'  '::'  st ]") : form_scope.

Notation "[ 'trace' ]" := [trace of [::]]
  (at level 0, format "[ 'trace' ]") : form_scope.

Notation "[ 'trace?' 'of' ts ]" := [trace of insubd [trace] ts]
  (at level 0, format "[ 'trace?'  'of'  ts ]") : form_scope.

Notation "[ 'trace' 'from' s ls ]" := [trace? of trace_from s ls]
  (at level 0, format "[ 'trace'  'from' s ls ]") : form_scope.

Notation "tr1 '<+>' tr2" := [trace of adjoin tr1 tr2]
  (at level 51, left associativity) : lts_scope.

Notation "st '<+' tr" := [trace of adjoin [:: val st] tr]
  (at level 49, right associativity) : lts_scope.

Notation "tr '+>' st" := [trace of adjoin tr [:: val st]]
  (at level 48, left associativity) : lts_scope.

Section Build.
Context {L : Type} (S : ltsType L).
Implicit Types (st : step S) (ts : traceSeq S) (tr : trace S).

Lemma nil_traceP : is_trace ([::] : traceSeq S).
Proof. done. Qed.
Canonical nil_trace := Trace nil_traceP.

Lemma singl_traceP st : is_trace [:: val st].
Proof. apply/andP; split=> //=; rewrite andbT; exact/(valP st). Qed.
Canonical singl_trace st := Trace (singl_traceP st).

Lemma insub_traceP ts : is_trace (insubd [trace] ts).
Proof. by rewrite val_insubd; case: ifP. Qed.
Canonical insub_trace ts := Trace (insub_traceP ts).

Lemma adjoin_traceP tr1 tr2 : is_trace (adjoin tr1 tr2).
Proof. 
  case: tr1=> [ts1]; case: tr2=> [ts2] /=.
  rewrite /adjoin /is_trace. 
  case: ifP=> [|?] //.
  move=> Hadj /andP[Hs1 Ha1] /andP[Hs2 Ha2].
  apply/andP; split.
  - by rewrite all_cat; apply/andP. 
  move: Hadj Hs1 Ha1 Hs2 Ha2.
  case: ts1=> [|st1 {}ts1] //=; rewrite cat_path.
  case: ts2=> [|st2 {}ts2] //= ?????; [exact/andP | exact/and3P].
Qed.
Canonical adjoin_trace tr1 tr2 := Trace (adjoin_traceP tr1 tr2).

Lemma adjoin_val tr1 tr2 : 
  adjoint tr1 tr2 -> tr1 <+> tr2 = tr1 ++ tr2 :> traceSeq S.
Proof. by rewrite /adjoin /=; case: ifP. Qed.

Lemma adjoin_cons_val st tr : 
  adjoint [trace :: st] tr -> st <+ tr = val st :: tr :> traceSeq S.
Proof. by rewrite /adjoin /=; case: ifP. Qed.

Lemma adjoin_rcons_val st tr : 
  adjoint tr [trace :: st] -> tr +> st = rcons tr (val st) :> traceSeq S.
Proof. by rewrite /adjoin -cats1 /=; case: ifP. Qed.

End Build.

Section EQ.
Context {L : eqType} (S : ltsType L).

Definition trace_eqMixin := Eval hnf in [eqMixin of trace S by <:].
Canonical trace_eqType := Eval hnf in EqType (trace S) trace_eqMixin.

End EQ.

Section Choice.
Context {L : choiceType} (S : ltsType L).

Definition trace_choiceMixin := 
  Eval hnf in [choiceMixin of trace S by <:].
Canonical trace_choiceType := 
  Eval hnf in ChoiceType (trace S) trace_choiceMixin.

End Choice.

Section Countable.
Context {L : countType} (S : ltsType L).

Definition trace_countMixin := 
  Eval hnf in [countMixin of trace S by <:].
Canonical trace_countType := 
  Eval hnf in CountType (trace S) trace_countMixin.

End Countable.

Section Theory. 
Context {L : Type} (S : ltsType L).
Implicit Types (l : L) (ls : seq L) (s : S).
Implicit Types (st : stepTuple S) (ts : traceSeq S) (tr : trace S).

Lemma trace_adj tr : sorted adj tr.
Proof. by move: (valP tr)=> /andP[]. Qed.

Lemma trace_steps tr : all is_step tr.
Proof. by move: (valP tr)=> /andP[]. Qed.

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

Lemma adjoint_adj st1 st2 :
  adjoint [:: st1] [:: st2] = adj st1 st2.
Proof. done. Qed.

Lemma adjoint_firstE st ts : 
  adjoint [:: st] ts = (dst st == fst_state (dst st) ts).
Proof. by case: ts=> //=; rewrite /adjoint eq_refl. Qed.

Lemma adjoint_lastE ts st : 
  adjoint ts [:: st] = (lst_state (src st) ts == src st).
Proof. done. Qed.

Lemma is_trace_cons st ts : 
  is_trace (st :: ts) = [&& is_step st, is_trace ts & adjoint [:: st] ts].
Proof. 
  rewrite /is_trace /adjoint /=.
  case: ts=> [|st' {}ts]; rewrite ?andbT //=.
  by rewrite [adj st st' && _]andbC !andbA /adj.
Qed.

Lemma is_trace_rcons ts st : 
  is_trace (rcons ts st) = [&& is_step st, is_trace ts & adjoint ts [:: st]].
Proof.
  rewrite /is_trace /adjoint all_rcons. 
  case: (lastP ts)=> [|{}ts st'] //=.
  - by rewrite eq_refl andbT.
  rewrite lst_state_rcons (sorted_rcons st).
  by rewrite /nilp /adj size_rcons last_rcons !andbA /=. 
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

Lemma size_states s ts : 
  size (states s ts) == (size ts).+1.
Proof. by rewrite /states; case: ts=> [|??] //=; rewrite size_map. Qed.
                         
Lemma states_rcons s ts st : s = fst_state (src st) ts -> 
  states s (rcons ts st) = rcons (states s ts) (dst st).
Proof. by case: ts=> [->|??] //=; rewrite map_rcons. Qed.

Lemma states_cat s ts1 ts2 : s = fst_state s ts2 -> 
  states s (ts1 ++ ts2) = states s ts1 ++ behead (states s ts2).
Proof. by rewrite /states map_cat; case: ts1; case: ts2=> //= ?? ->. Qed.

Lemma adjoin0s tr : 
  [trace] <+> tr = tr.
Proof. by apply/val_inj=> /=; rewrite adjoin_val ?adjoint0s //=. Qed.  

Lemma adjoins0 tr : 
  tr <+> [trace] = tr.
Proof. by apply/val_inj=> /=; rewrite adjoin_val ?adjoints0 ?cats0 //=. Qed.

Lemma trace_from_cons s l ls : has_trans l s -> 
  exists s', trace_from s (l :: ls) = (mk_step l s s') :: trace_from s' ls.
Proof.
  rewrite has_transE /trace_from /isSome /=.
  case: (pick_trans l s)=> //= s' _.
  by exists s'. 
Qed.

Lemma trace_from_fst_state s ls : 
  lts_lang s ls -> s = fst_state s (trace_from s ls).
Proof. 
  rewrite /lts_lang /trace_lang=> [[]].
  case=> /= []; case=> [|st {}ts] /= Htr /eqP Hs -> //.
  suff: has_trans (lbl st) s.
  - by move=> /(trace_from_cons (labels ts)) [s'] ->.
  move: Htr; rewrite /is_trace=> /andP[] /= /andP[].
  rewrite /is_step Hs=> ? _ _. 
  by apply/has_transP; exists (dst st).
Qed.  

Lemma trace_from_is_trace s ls : 
  lts_lang s ls -> is_trace (trace_from s ls).
Proof. 
  rewrite /lts_lang /trace_lang=> [[]].
  case=> /= [] ts; move: ls. 
  elim: ts=> [|st {}ts] /=. 
  - by move=> ??? ->.
  move=> IH ls Htr /eqP Hs -> //.
  admit.
  (* suff: has_trans (lbl st) s. *)
  (* - by move=> /(trace_from_cons (labels ts)) [s'] ->. *)
  (* move: Htr; rewrite /is_trace=> /andP[] /= /andP[]. *)
  (* rewrite /is_step Hs=> ? _ _.  *)
  (* by apply/has_transP; exists (dst st). *)
Admitted.  

End Theory.

End Trace.


Module Export Simulation.

Module Simulation.
Section ClassDef. 

(* TODO: simulation between lts labelled by different labels? *)
Context {L : Type} (S T : ltsType L).
Implicit Types (R : hrel S T).

Record mixin_of R := Mixin {
  _ : forall (l : L) (s1 : S) (t1 t2 : T), 
        R s1 t1 -> t1 --[l]--> t2 -> exists2 s2, 
        R s2 t2  & s1 --[l]--> s2;  
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
Context {L : eqType} {S T : ltsType L}.
Implicit Types (R : S ~>~ T).

Lemma sim_step R l s1 t1 t2 :
  R s1 t1 -> (t1 --[l]--> t2) -> exists2 s2, R s2 t2 & (s1 --[l]--> s2).
Proof. case: R=> ? [[H]] /=; exact/H. Qed.

Lemma sim_lang R s t : 
  R s t -> lts_lang t ≦ lts_lang s.
Proof. 
  move=> HR w [[tr Htr]] + ->; clear w.
  rewrite /lts_lang /trace_lang /= => /eqP Hh. 
  suff: (exists (tr' : trace S), 
           [/\ R (lst_state s tr') (lst_state t tr), 
               labels tr = labels tr' 
             & s == fst_state s tr'
           ]).
  - by move=> [tr' []] ???; exists tr'.
  move: Htr Hh; elim/last_ind: tr=> [|{}tr st IH] /=.
  - by exists [trace] => /=.
  rewrite is_trace_rcons=> /and3P[Hst Htr Hj].
  rewrite fst_state_rcons -fst_state_src. 
  case: (nilp tr)/nilP=> [->|Hnil] /=. 
  - move: Hst; rewrite /is_step=> /[swap] <- => Hs. 
    move: (sim_step HR Hs)=> [s' HR' Hs'].
    pose st' := step_of Hs'. 
    by exists [trace :: st']. 
  rewrite (fst_stateNnil t) // => Ht.
  move: (IH Htr Ht); clear IH. 
  move=> [tr' []] /[swap].
  rewrite !labels_rcons.    
  move: Hj; rewrite adjoint_lastE=> /eqP. 
  rewrite (lst_stateNnil t (src st))=> // ->.
  move: Hst; rewrite /is_step=> Hs Hlbl HRl.
  move: (sim_step HRl Hs)=> [s'].
  move=> HR' Hs' /eqP Hfst.
  have: ~~ nilp tr'.
  - rewrite /nilp -size_labels -Hlbl size_labels. 
    by move: Hnil=> /nilP.
  move=> /nilP Hnil'.
  pose st' := step_of Hs'.
  exists (tr' +> st'). 
  rewrite !adjoin_rcons_val; last first; [|split].
  - by rewrite /adjoint /= (lst_stateNnil s) /=.  
  - by rewrite !lst_state_rcons /=.
  - by rewrite labels_rcons Hlbl.
  rewrite fst_state_rcons Hfst -fst_state_src. 
  by apply/eqP/fst_stateNnil.
Qed.

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
  R s1 t1 -> (s1 --[l]--> s2) -> exists2 t2, R s2 t2 & (t1 --[l]--> t2).
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
