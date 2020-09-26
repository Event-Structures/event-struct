From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order.
From mathcomp Require Import eqtype fingraph path. 
From event_struct Require Import utilities EventStructure.
From Coq Require Import Arith.

Section confluence.
Context {val : eqType}.
Notation exec_event_struct := (@exec_event_struct val).
Notation cexec_event_struct := (@cexec_event_struct val).
Implicit Types (x : var) (a : val) (t : tid).
Notation label := (@label val).
Notation n := (@n val).
Notation lab := (@lab val).
Notation ofrf := (@ofrf val).
Notation ofpred := (@ofpred val).

Definition opredn (e' : exec_event_struct) := 
  ord_dom_to_nat (ofpred e') (omap (@nat_of_ord _)).

Definition ofrfn (e' : exec_event_struct)  := 
  ord_dom_to_nat (ofrf e') (omap (@nat_of_ord _)).

Definition olabn (e' : exec_event_struct)  := 
  ord_dom_to_nat (lab e') some.

Definition ord n : ssrbool.pred nat := fun m => m < n.

Definition ois_read l := 
  if l is some l then @is_read val l else false.

Section funn_properties.
Context {es : exec_event_struct} (m : nat).

Lemma opredn_lt k: opredn es k = Some m -> m < k.
Proof. Admitted.

Lemma ofrfn_lt k: ofrfn es k = Some m -> m < k.
Proof. Admitted.

Lemma olabn_correct: m < n es -> olabn es m.
Proof. Admitted.

Lemma opredn_correct k: m < n es -> (opredn es m = some k) -> k < m.
Proof. Admitted.

Lemma ofrfn_correct1 k:
    reflect (ofrfn es m = some k) (ocompatible (olabn es m) (olabn es k)).
Proof. Admitted.

Lemma ofrfn_correct2:
      ois_read (olabn es m) -> ofrfn es m.
Proof. Admitted.

End funn_properties.

Section evstruct_from_nat.

Context {N : nat} (* size of nex event structure *)
         {flabn : nat -> option label}
         {fpredn ffrfn : nat -> option nat}.
Hypothesis 
   (flabn_correct: forall m, m < N -> flabn m)
  (fpredn_correct: forall m k, m < N -> (fpredn m = some k) -> k < m)
   (ffrfn_correct1: forall m k, 
      (ffrfn m = some k) -> (ocompatible (flabn m) (flabn k)))
   (ffrfn_correct2: forall n,
      ois_read (flabn n) -> ffrfn n).

Definition make_es : exec_event_struct. Admitted.

Lemma olabn_make_es: olabn make_es =1 flabn.
Proof. Admitted.

Lemma opredn_make_es: opredn make_es =1 fpredn.
Proof. Admitted.

Lemma ofrfn_make_es: ofrfn make_es =1 ffrfn.
Proof. Admitted.

End evstruct_from_nat.

Definition is_mono (f : nat -> nat) es es' := 
  ((({in ord (n es), injective f}) *
    ({in ord (n es), (opredn es') \o f =1 (omap f) \o (opredn es)})) *
   (({in ord (n es), (ofrfn es') \o f =1 (omap f) \o (ofrfn es)}) *
    ({in ord (n es), (olabn  es') \o f =1 olabn es})))%type.

Definition sub_evstuct es es' := exists f, is_mono f es es'.

Lemma is_mono_le f es es': is_mono f es es' -> n es <= n es'.
Proof. Admitted.

Lemma omap_id {T}: omap (@id T) =1 id.
Proof. by case. Qed.

Context {es es1 es2 : exec_event_struct}.
Hypothesis (I1 : is_mono id es es1) (I2 : is_mono id es es2).
Notation N := (n es1 + n es2 - n es).


Lemma intersec_sync_lab: {in ord (n es), olabn es1 =1 olabn es2}.
Proof. move=> ? L. move: I1 I2. by do ? case=> [[?? [? /(_ _ L) /=->]]]. Qed.

Lemma intersec_sync_pred: {in ord (n es), opredn es1 =1 opredn es2}.
Proof. move=> ? L. move: I1 I2. by do ?case=> [[? /(_ _ L) /= -> ?]]. Qed.

Lemma intersec_sync_rf: {in ord (n es), ofrfn es1 =1 ofrfn es2}.
Proof. move=> ? L. move: I1 I2. by do ?case=> [[??[/(_ _ L) /= -> ?]]]. Qed.


Definition i2 := fun m => if m < n es then m else m + (n es1 - n es).

Definition i1 : nat -> nat := id.

Lemma inj_i2 : {in ord (n es2), injective i2}.
Proof. move=> ???. rewrite /i2. do ?case: ifP; slia. Qed.

(*Lemma inj_i1 : injective i1.
Proof. by []. Qed.*)

Definition olabn_sync := fun m =>
  if m < n es1 then
    olabn es1 m
  else olabn es2 (m - (n es1 - n es)).

Lemma olabn_sync_correct m: m < N  -> olabn_sync m.
Proof. rewrite /olabn_sync. case: ifP=> *; apply /olabn_correct; slia. Qed.

Lemma olabn_syncC1: {in ord (n es1), olabn_sync \o i1 =1 olabn es1}.
Proof. move=> ?/=. by rewrite /i1 /olabn_sync /in_mem /ord /= =>->. Qed.

Lemma olabn_syncC2: {in ord (n es2), olabn_sync \o i2 =1 olabn es2}.
Proof.
  move=> k /=?. rewrite /i2 /olabn_sync /in_mem /ord /=. do ?case: ifP; try slia.
  { by move /intersec_sync_lab =>->. }
  { move /is_mono_le: I1. slia. }
  have -> //: (k + (n es1 - n es) - (n es1 - n es)) = k by slia.
Qed.

Definition opredn_sync := fun m =>
  if m < n es1 then
    opredn es1 m
  else if opredn es2 (m - (n es1 - n es)) is some y then
    some (if y < n es then
      y
    else y + (n es1 - n es))
  else None.

Lemma opredn_sync_correct m k: m < N -> (opredn_sync m = some k) -> k < m.
Proof.
  rewrite /opredn_sync. case: ifP; do ?ocase.
  { move=> *. by apply /(@opredn_correct es1). }
  move=> H ??.
  have /opredn_correct /(_ H): (m - (n es1 - n es)) < (n es2) by slia.
  case: ifP=> ?? [<-]; slia.
Qed.

Lemma opredn_syncC1: 
  {in ord (n es1), opredn_sync \o i1 =1 (omap i1) \o opredn es1}.
Proof. move=> ?/=. by rewrite /i1 /opredn_sync /in_mem /ord /= omap_id =>->. Qed.

Lemma opredn_syncC2: 
  {in ord (n es2), opredn_sync \o i2 =1 (omap i2) \o opredn es2}.
Proof.
  move=> k /=?. rewrite /i2 /opredn_sync /in_mem /ord /=. do ?case: ifP; try slia.
  { move=> L. move /intersec_sync_pred: (L)=>->.
    case: I2=> [[? /(_ k L) /= -> ?]].
    case E: (opredn es k)=> //=. case: ifP E=> // ? /opredn_lt. slia. }
  { move /is_mono_le: I1. slia. }
  have->: (k + (n es1 - n es) - (n es1 - n es)) = k by slia.
  by ocase.
Qed.

Definition ofrfn_sync := fun m =>
if m < n es1 then
  ofrfn es1 m
else if ofrfn es2 (m - (n es1 - n es)) is some y then
  some (if y < n es then
    y
  else y + (n es1 - n es))
else None.

Lemma ofrfn_sync_correct1 m k:
  (ofrfn_sync m = some k) -> (ocompatible (olabn_sync m) (olabn_sync k)).
Proof.
  rewrite /ofrfn_sync /olabn_sync. case: ifP=> [? H| ?].
  { move /ofrfn_lt: (H) (H)=> ?. have->: k < n es1 by slia.
    by move /ofrfn_correct1. }
  ocase. case: ifP=> [L /ofrfn_correct1 ? [<-]|? /swap [[<-]]].
  { move /is_mono_le: I1. case: ifP=> //; try slia.
    by move: (intersec_sync_lab _ L)=>->. }
  case: ifP; try slia. move=> _ /ofrfn_correct1. 
  by rewrite -addnBA// subnn addn0.
Qed.

Lemma ofrfn_sync_correct2 m: ois_read (olabn_sync m) -> ofrfn_sync m.
Proof.
  rewrite /olabn_sync /ofrfn_sync. case: ifP=> [? /ofrfn_correct2 //|].
  move=> ? /ofrfn_correct2. by ocase.
Qed.

Lemma ofrfn_syncC1: 
  {in ord (n es1), ofrfn_sync \o i1 =1 (omap i1) \o ofrfn es1}.
Proof. move=> ?/=. by rewrite /i1 /ofrfn_sync /in_mem /ord /= omap_id =>->. Qed.

Lemma ofrfn_syncC2: 
  {in ord (n es2), ofrfn_sync \o i2 =1 (omap i2) \o ofrfn es2}.
Proof.
  move=> k /=?. rewrite /i2 /ofrfn_sync /in_mem /ord /=. do ?case: ifP; try slia.
  { move=> L. move /intersec_sync_rf: (L)=>->.
    case: I2=> [[?? [/(_ k L) /= -> ?]]].
    case E: (ofrfn es k)=> //=. case: ifP E=> // ? /ofrfn_lt. slia. }
  { move /is_mono_le: I1. slia. }
  have->: (k + (n es1 - n es) - (n es1 - n es)) = k by slia.
  by ocase.
Qed.

Definition es_sync := 
  make_es 
    olabn_sync_correct
    opredn_sync_correct
    ofrfn_sync_correct1
    ofrfn_sync_correct2.

Theorem confluence: 
  {es_sync | sub_evstuct es1 es_sync /\ sub_evstuct es2 es_sync}.
Proof.
  exists es_sync; split; [exists i1| exists i2].
  { do ? split=> //.
    { move=> ? /opredn_syncC1 /=. by rewrite opredn_make_es. }
    { move=> ? /ofrfn_syncC1 /=. by rewrite ofrfn_make_es. }
    move=> ? /olabn_syncC1 /=. by rewrite olabn_make_es. }
  do ?split=> //.
  { exact: inj_i2. }
  { move=> k /opredn_syncC2 /=. by rewrite opredn_make_es. }
  { move=> ? /ofrfn_syncC2 /=. by rewrite ofrfn_make_es. }
  move=> ? /olabn_syncC2 /=. by rewrite olabn_make_es.
Qed.

End confluence.

