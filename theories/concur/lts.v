From RelationAlgebra Require Import lattice monoid rel.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq path. 
From eventstruct Require Import utils relalg.

(******************************************************************************)
(* This file provides a theory of labelled transition systems.                *)
(* TODO.                                                                      *)
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
  base  : Equality.class_of S;
  mixin : mixin_of L base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Equality.class_of.

Structure type (L : Type) := Pack { sort; _ : class_of sort L }.

Local Coercion sort : type >-> Sortclass.

Variables (S : Type) (L : Type) (cT : type L).

Definition class := let: Pack _ c as cT' := cT return class_of (sort cT') L in c.
Definition clone c of phant_id class c := @Pack S c.

Definition pack :=
  fun bS b & phant_id (@Equality.class bS) b =>
  fun m => Pack (@Class S L b m).

Definition eqType := @Equality.Pack cT class.
End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Equality.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
End Exports.

End LTS.

Export LTS.Exports.

Notation ltsType := LTS.type.
Notation LTSType S L m := (@LTS.pack S L _ _ id m).

Section Def.
Context {L : Type} (S : ltsType L).

Definition trans : L -> rel S := LTS.trans (LTS.class S).

End Def.

Module Export Syntax.
Notation "s1 '--[' l ']-->' s2" := (trans l s1 s2) : lts_scope.
Notation "s1 '-->' s2"  := (exlab trans)   : lts_scope.
Notation "s1 '-->?' s2" := (exlab trans)^? : lts_scope.
Notation "s1 '-->+' s2" := (exlab trans)^+ : lts_scope. 
Notation "s1 '-->*' s2" := (exlab trans)^* : lts_scope.
End Syntax.

End LTS.

(* Context {L : Type} {S : ltsType L}. *)
(* Variable (l : L) (s1 s2 : S). *)
(* Check (s1 --[l]--> s2). *)

Module Export Step. 

Section Def.
Context {L : Type} (S : ltsType L).

Record step : Type := mk_step {
  lbl : L; src : S; dst : S;  
}.

Definition is_step : pred step := 
  fun s => (src s) --[lbl s]--> (dst s).

(* TODO: better name? *)
Definition lnk : rel step := 
  fun s t => dst s == src t. 

Definition rev_step : step -> step := 
  fun s => mk_step (lbl s) (dst s) (src s).

End Def.

Prenex Implicits lbl src dst.
Prenex Implicits is_step lnk rev_step.

Section EQ. 
Context {L : eqType} (S : ltsType L).

Definition prod_of_step : step S -> L * S * S := 
  fun s => (lbl s, src s, dst s).

Lemma prod_of_step_inj : injective prod_of_step.
Proof. 
  rewrite /prod_of_step; move=> x y /= []. 
  by case x; case y=> /= ?????? -> -> ->. 
Qed.

Definition step_eqMixin := InjEqMixin prod_of_step_inj.
Canonical step_eqType := Eval hnf in EqType (step S) step_eqMixin.

(* Lemma prod_of_step_inj : injective (prod_of_step : step S -> L * S * S). *)
(* Proof.  *)
(*   case=> [s1 H1]; case=> [s2 H2] /=. *)
(*   move=> /prod_of_step_tup_inj. *)
(*   move: H2=> /[swap]; move: H1=> /[swap] -> H1 H2. *)
(*   have ->: H1 = H2=> //; exact/bool_irrelevance. *)
(* Qed. *)

(* Definition step_eqMixin := InjEqMixin prod_of_step_inj. *)
(* Canonical step_eqType := Eval hnf in EqType (step S) step_eqMixin. *)

End EQ.

Section Theory.
Context {L : Type} (S : ltsType L).
Implicit Types (st : step S).

Lemma lnk_rev st : lnk st (rev_step st).
Proof. by rewrite /lnk. Qed.

Lemma rev_lnk st : lnk (rev_step st) st.
Proof. by rewrite /lnk. Qed.

End Theory.

End Step.


Module Export Trace. 

Notation trace_seq S := (seq (step S)).

Section Def. 
Context {L : Type} (S : ltsType L).

Definition is_trace : pred (trace_seq S) := 
  fun s => (all is_step s) && (sorted lnk s).

Structure trace : Type := Trace { 
  trace_val :> trace_seq S; 
  _         :  is_trace trace_val;
}.

Canonical trace_subType := Eval hnf in [subType for trace_val].

Implicit Types (tr : trace).

Lemma trace_steps tr : all is_step tr.
Proof. by case: tr; rewrite /is_trace=> ? /= /andP[]. Qed.

Lemma trace_lnk tr : sorted lnk tr.
Proof. by case: tr; rewrite /is_trace=> ? /= /andP[]. Qed.

(* TODO: better name? *)
Definition joint : rel (trace_seq S) := 
  fun s1 s2 => 
    match s2 with 
    | [::]      => true
    | st :: s2 => lnk (last (rev_step st) s1) st
    end.

Definition labels : trace_seq S -> seq L := map lbl. 

Definition states : trace_seq S -> seq S := 
  fun s => 
    match s with 
    | [::]    => [::]
    | st :: s => src st :: dst st :: map dst s
    end. 

Definition traces_at : S -> pred trace := 
  fun s tr => s == head s (states tr).

(* TODO: this is actually a fmap on (A -> Prop) functor. *)
Definition ltslang : S -> lang L := 
  fun s w => exists tr, w = labels tr /\ traces_at s tr.

Definition mk_trace tr mkTr : trace :=
  mkTr (let: Trace _ trP := tr return is_trace tr in trP).

End Def. 

Arguments joint : simpl never.

Section Seq.
Context {L : Type} (S : ltsType L).
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

Section Theory. 
Context {L : Type} (S : ltsType L).
Implicit Types (st : step S) (s : trace_seq S) (tr : trace S).

Lemma joint0s s :
  joint [::] s.
Proof. by rewrite /joint; case: s=> [|??] //=; rewrite rev_lnk. Qed.

Lemma joints0 s :
  joint s [::].
Proof. by rewrite /joint. Qed.

Lemma joint_cons st s1 s2 :
  joint s1 (st :: s2) = joint s1 [:: st]. 
Proof. by rewrite /joint; case: s2=> [|??] //=; rewrite last_rcons. Qed.

Lemma joint_rcons st s1 s2 :
  joint (rcons s1 st) s2 = joint [:: st] s2. 
Proof. by rewrite /joint; case: s2=> [|??] //=; rewrite last_rcons. Qed.

Lemma cons_is_trace st s : 
  is_step st -> joint [:: st] s -> is_trace s -> is_trace (st :: s).
Proof. 
  move=> Hs Hj Htr; rewrite /is_trace /=.
  repeat (apply/andP; split)=> //.
  - by move: Htr; rewrite /is_trace=> /andP[]. 
  move: Hj Htr; case: s=> [|st' {}s] //=.
  rewrite joint_cons /joint /= => Hlnk.
  rewrite /is_trace /= => /andP[/andP[]].
  move=> ???; exact/andP.
Qed.

Lemma is_trace_rcons s st : 
  is_trace (rcons s st) = [&& is_step st, is_trace s & joint s [:: st]].
Proof. 
  rewrite /is_trace all_rcons -andbA -andbA.
  apply/andb_id2l=> _; apply/andb_id2l=> _.
  rewrite (sorted_rcons s (rev_lnk st)). 
  by rewrite /joint.
Qed.
                         
Lemma states_cons st s : joint [:: st] s ->
  states (st :: s) = src st :: dst st :: behead (states s).
Proof. admit. Admitted.
    
Lemma behead_states s :
  behead (states s) = map dst s.
Proof. by rewrite /states; case: s. Qed. 

Lemma states_rcons_src s st : 
  states (rcons s st) = (map src s) ++ [:: src st; dst st].
Proof. admit. Admitted.

Lemma states_rcons s st : ~~ nilp s -> is_trace s -> joint s [:: st] ->
  states (rcons s st) = rcons (states s) (dst st).
Proof. 
  move=> /(elimN nilP).
  case: (lastP s)=> //=.
  move=> {}s st' _.
  rewrite is_trace_rcons=> /andP[Htr Hj]. 
  rewrite joint_rcons /joint /= => Hlnk.
  rewrite !states_rcons_src map_rcons.
  rewrite -cats1 -cats1 -catA -catA /=.
  by move: Hlnk; rewrite /lnk=> /eqP ->.
Qed.  

Lemma states_cat s1 s2 : ~~ nilp s1 -> is_trace s1 -> joint s1 s2 -> 
  states (s1 ++ s2) = states s1 ++ behead (states s2).
Proof. 
  rewrite behead_states; move=> /(elimN nilP).
  move: s2; elim/last_ind: s1=> [|{}s1 st IH] s2 _ //=.
  case: (nilp s1)/nilP=> [->|Hnil] //=.
  rewrite is_trace_rcons=> /andP[Hs /andP[Htr Hj]].
  rewrite joint_rcons cat_rcons IH //. 
  rewrite states_rcons ?cat_rcons //=; exact/nilP.
Qed.

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

End Simulation.

Export Simulation.Exports.

Notation sim := Simulation.type.

Module Syntax. 
Notation "S ~>~ T" := (sim S T) (at level 50) : lts_scope.
End Syntax. 

Section Theory.
Import Syntax. 
Context {L : Type} {S T : ltsType L}.
Implicit Types (R : S ~>~ T).

Lemma sim_step R l s1 t1 t2 :
  R s1 t1 -> (t1 --[l]--> t2) -> exists s2, R s2 t2 /\ (s1 --[l]--> s2).
Proof. case: R=> ? [[H]] /=; exact/H. Qed.

(* Lemma sim_stepE R l :  *)
(*   (R : hrel S T) ⋅ (tr l : hrel T T) ≦ (tr l : hrel S S) ⋅ (R : hrel S T). *)
(* Proof. admit. Admitted. *)

Lemma sim_traces R s t : 
  R s t -> ltslang s ≦ ltslang t.
Proof. 
  move=> HR w [[tr Htr]] [->]; clear w. 
  rewrite /ltslang /traces_at /=.
  rewrite /labels /= => /eqP.
  move: Htr; elim/last_ind: tr=> [|{}tr st IH] /=.
  - by exists [trace] => /=.
  rewrite is_trace_rcons=> /andP[Hs /andP[Htr Hj]].
  case: (nilp tr)/nilP=> [->|Hnil] /=.
  - admit.
  rewrite states_rcons //; last exact/nilP.
  rewrite headI /=.  
  admit. 
Admitted.

End Theory.

End Simulation. 


