From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order.
From mathcomp Require Import eqtype fingraph path. 
From event_struct Require Import utilities eventstructure relations inhtype.

Section TransitionSystem.

Context {val : eqType}.

Notation exec_event_struct := (@exec_event_struct val).
Notation cexec_event_struct := (@cexec_event_struct val).

Notation label := (@label val val).

Implicit Types (x : var) (a : val) (es : exec_event_struct).

(* Section with definitions for execution graph with added event *)
Section AddEvent.

(* execution graph in which we want to add l *)
Context (es : exec_event_struct).

Notation n      := (n es).
Notation lab    := (lab es).
Notation fpred  := (fpred es).
Notation frf    := (frf es).

Structure add_label :=
  Add {
    lb     : label;
    opred  : option 'I_n;
    owrite : is_read lb -> {k : 'I_n | compatible (ext lab k) lb}
  }.

Variable al : add_label.

(* label of an event which we want to add     *)
Notation l := (lb al).

(* predecessor of the new event (if it exists) *)
Notation op := (opred al).

(* if event is `Read` then we should give `Write` from wich we read *)
Notation ow := (owrite al).

Definition add_lab : 'I_n.+1 -> label := 
  @add (fun=> label) n lab l.

Definition add_fpred : forall m : 'I_n.+1, option 'I_m := 
  @add (option \o ordinal) n fpred op.

Arguments add_lab : simpl never.

Lemma is_read_add_lab {r : 'I_n} :
  is_read_ext add_lab r -> is_read_ext lab r.
Proof. rewrite /add_lab ext_add //. case: r=> /= *. slia. Qed.

Lemma add_lab_compatible {w r : nat}
  (_ : compatible_ext lab w r) : compatible_ext add_lab w r.
Proof. 
  rewrite /add_lab rel_ext // => [[]]; 
  rewrite /rdom /codom /compatible=> [[//]]. by case. 
Qed.

Lemma is_read_add_lab_n: is_read_ext add_lab n = is_read l.
Proof. by rewrite /add_lab ext_add_n. Qed.

Lemma is_read_add_lab_n_aux: is_read_ext add_lab n -> is_read l.
Proof. by rewrite is_read_add_lab_n. Qed.

Lemma compatible_add_lab (r : 'I_n) : 
  compatible (ext lab r) l -> compatible_ext add_lab r n.
Proof. 
  rewrite /add_lab /comp2 ext_add ?ext_add_n //. 
  case: r=> /= *. slia.
Qed.

Definition  ow_add_lab (is_r : is_read_ext add_lab n) :
  {r : 'I_n |compatible_ext add_lab r n} :=
   let w := ow (is_read_add_lab_n_aux is_r) in
     @exist _ _ (sval w) (compatible_add_lab _ (svalP w)).

Definition add_frf : forall
  (r : 'I_n.+1)
  (is_r : is_read_ext add_lab r),
  { w : 'I_r | compatible_ext add_lab w r } := 
  let T (r : nat) := 
      forall (is_r : is_read_ext add_lab r), 
        { w : 'I_r | compatible_ext add_lab w r }
  in
  let frf' (r : 'I_n) : T r := 
      fun is_r =>
        let fP (w : 'I_r) := @add_lab_compatible w r in
        sproof_map fP (frf r (is_read_add_lab is_r))
  in
  add frf' ow_add_lab.

Lemma sval_add_frf (e1 : 'I_n.+1) (e2 : 'I_n) p p' : e1 = e2 :> nat ->
  sval (add_frf e1 p) = sval (frf e2 p') :> nat.
Proof.
  case: e1 e2 p p'=> ? L1 [? L2 /= P1 P2] E. case: _ / E P1 P2 L1 L2 => *.
  rewrite /add_frf add_lt /=. do ?apply /congr1. exact: eq_irrelevance.
Qed.

Definition add_event := Pack n.+1 add_lab add_fpred add_frf.

Lemma ofpred_add_event e : ofpred add_event e =
  if e == n then omap (@nat_of_ord n) op else ofpred es e.
Proof.
  rewrite /ofpred. insub_case=> L; insub_case=> ?; try case : ifP; try slia.
  { move=> ?. apply /congr1. by rewrite /add_fpred add_lt. }
  move=> /eqP /esym E. move: E L. case: _ / => ?. 
  by rewrite /add_fpred add_ord_max.
Qed.

Definition owr := 
  (if is_read l as is_r return (is_read l = is_r -> option nat) then
    fun pf => some (nat_of_ord (sval (ow pf))) 
  else fun=> none) erefl.

Lemma sval_oread {e}: 
  (e == n = false) -> 
  omap ((@nat_of_ord n) \o sval) (oread es e) =
  omap ((@nat_of_ord n.+1) \o sval) (oread add_event e).
Proof.
  move=> ?. rewrite /oread. insub_case; dcase; (try slia)=> ? L.
  case R: (is_read_ext lab e); [rewrite insubT | rewrite insubF]=> //=;
  [rewrite insubT | rewrite insubF]=> //=.
  all: rewrite /add_lab ext_add //; slia.
Qed.

Arguments oread : simpl never.

Lemma ofrf_add_event e: ofrf add_event e = 
  if e == n then owr else ofrf es e.
Proof.
  rewrite /ofrf/=. case: ifP=> [/eqP ->| efn].
  { rewrite /owr. dcase.
    { rewrite /oread /=. insub_case=> [? R|]; last slia.
      rewrite insubT /= ?is_read_add_lab_n // => R'. 
      rewrite /add_frf add_ord_max /=. do? apply /congr1. 
      exact: eq_irrelevance. }
    rewrite /oread /=. insub_case=> *. 
    by rewrite insubF // is_read_add_lab_n. }
  case H: (oread add_event e)=> [[/=]|];
  move: (H) (sval_oread efn)=>->/=; case H': (oread es e) => //= [[/=]][?].
  exact /congr1 /sval_add_frf.
Qed.

(*Lemma ica_add_event e1 e2: 
  ica add_event e1 e2 = 
    if (e2 == n) then
       (omap (@nat_of_ord n) op == some e1) || (owr == some e1)
    else ica es e1 e2.
Proof. 
  rewrite /ica /succ /rf ofrf_add_event ofpred_add_event. by case: ifP. 
Qed.*)

Lemma ica_add_event e1 e2: 
  ica add_event e1 e2 =
  (ica es e1 e2) || 
  ((e2 == n) && ((omap (@nat_of_ord n) op == some e1) || (owr == some e1))).
Proof.
  rewrite /ica /succ /rf ofrf_add_event ofpred_add_event. case: ifP=>/=.
  { move /eqP->. by rewrite ofpred_n ?ofrf_n. }
  by rewrite orbF.
Qed.

Hypothesis consist : consistency es.
Hypothesis ncf_rf : forall e, owr = some e -> ~~ (cf add_event n e).

Arguments cfP {_ _ _ _}.
Arguments closureP {_ _ _}.
Notation step := (Relation_Operators.rtn1_trans).

Lemma ca_add_event e1 e2 (N : e2 != n) : ca es e1 e2 = ca add_event e1 e2.
Proof.
  apply/(refleqP closureP closureP). 
  split; move: N=> /swap; elim; try constructor.
  all: move=> y ? I ? H ?; apply /(step _ _ _ y)=> //.
  { rewrite ica_add_event; apply /orP. by left. }
  { apply/H. case /irel_rt_cl /ca_rfield /orP: I=> [|/andP[]]; slia. }
  { move: I. rewrite ica_add_event=> /orP[]// /andP[]. slia. }
  apply /H.
  case/irel_rt_cl /ca_rfield /orP: (I) (I)=> /= [|/andP[?? /ica_lt]]; slia.
Qed.

Lemma icf_add_event e1 e2  (_ : e1 != n) (_ : e2 != n) :
  icf es e1 e2 = icf add_event e1 e2.
Proof.
  rewrite /icf !ofpred_add_event /=. do ?case: ifP; try slia.
  by rewrite /add_lab ?ext_add.
Qed.

Lemma cf_add_event e1 e2  (_ : e1 != n) (_ : e2 != n) :
  cf es e1 e2 = cf add_event e1 e2.
Proof.
  apply /(refleqP cfP cfP). do ?apply /exists_eq => ?. 
  rewrite -?ca_add_event //. apply /Bool.eq_iff_eq_true.
  do 2?apply /and_eq=> /ca_rfield /orP[|/andP[]]*; rewrite icf_add_event; slia.
Qed.

Lemma consist_add_event: consistency add_event.
Proof.
  rewrite /consistency. apply /forallP=> e1. apply /forallP => e2.
  apply /implyP=> /eqP. rewrite ofrf_add_event. case: ifP=> [/eqP->/ncf_rf|]//.
  case: e1 e2=> /= x? [y? /=]. case yEn: (x == n).
  { move /eqP: yEn=>-> ? /ofrf_le. slia. }
  move=> E. move /rff_consist: consist => /apply cf. apply /negP=> cf'.
  apply /cf. rewrite cf_add_event; slia.
Qed.

End AddEvent.

Definition tr_add_event es1 es2 := exists al, es2 = add_event es1 al.

Notation "es1 '-->' es2" := (tr_add_event es1 es2) (at level 0).

Definition ltr_add_event es1 al es2 := es2 = add_event es1 al.

Notation "es1 '--' al '-->' es2" := (ltr_add_event es1 al es2) (at level 0).

End TransitionSystem.
