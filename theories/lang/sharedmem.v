From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From mathcomp Require Import eqtype choice finfun finmap tuple.
From eventstruct Require Import utils inhtype ident lts relaxed.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.
Local Open Scope fset_scope.
Local Open Scope ident_scope.

Module SharedMem.

Section Def.
Context {Addr Val : inhType}.

Local Notation null := (inh : Addr).
Local Notation v0   := (inh : Val).

Definition state := 
  { fsfun Addr -> Val for fun x => v0 }.

Variant label := 
  | Read  of Addr & Val 
  | Write of Addr & Val 
  | Bot
  .

Definition typ : label -> Lab.typ :=
  fun l => match l with
  | Read  _ _ => Lab.Read
  | Write _ _ => Lab.Write
  | Bot       => Lab.Undef
  end.

Definition addr : label -> Addr :=
  fun l => match l with
  | Read  x _ => x
  | Write x _ => x
  | Bot       => null
  end.

Definition value : label -> Val :=
  fun l => match l with
  | Read  _ v => v
  | Write _ v => v
  | Bot       => v0
  end.

End Def.

Arguments state _ _ : clear implicits.
Arguments label _ _ : clear implicits.

Section Encode. 
Context {Addr Val : inhType}.

Definition enc_lab : (label Addr Val) -> Addr * Val + Addr * Val + unit := 
  fun l => match l with 
  | Read  x v => inl (inl (x, v))
  | Write x v => inl (inr (x, v))
  | Bot       => inr tt
  end.

Definition dec_lab : Addr * Val + Addr * Val + unit -> (label Addr Val) := 
  fun l => match l with 
  | inl (inl (x, v)) => Read x v
  | inl (inr (x, v)) => Write x v
  | inr _            => Bot
  end.

Lemma enc_dec_labK : 
  cancel enc_lab dec_lab.
Proof. by case. Qed. 

End Encode.

Module Export Exports.
Implicit Types (A V : inhType).

Definition label_eqMixin A V := 
  CanEqMixin (@enc_dec_labK A V).
Canonical label_eqType A V := 
  Eval hnf in EqType _ (label_eqMixin A V).

Definition label_choiceMixin A V := 
  CanChoiceMixin (@enc_dec_labK A V).
Canonical label_choiceType A V := 
  Eval hnf in ChoiceType _ (label_choiceMixin A V).

End Exports.


Module Export LTS.
Section LTS.
Context {Addr Val : inhType}.
Local Notation state := (state Addr Val).
Local Notation label := (label Addr Val).
Implicit Types (m : state) (l : label).

Definition read_trans l m m' := 
  let x := addr l in 
  let v := value l in 
  (typ l == Lab.Read) && (m x == v) && (m' == m).

Definition write_trans l m m' := 
  let x := addr l in 
  let v := value l in 
  (typ l == Lab.Write) && (m' == [fsfun m with x |-> v]).

Definition ltrans l m m' := 
  (read_trans l m m') || (write_trans l m m').

Definition enabled l m := 
  match l with 
  | Read  x v => m x == v
  | Write x v => true
  | Bot       => false
  end.

Lemma enabledP l m :
  reflect (exists m', ltrans l m m') (enabled l m).
Proof. 
  rewrite /ltrans /read_trans /write_trans /enabled.
  case: l=> [x v | x v |]; try constructor=> //=; last first.
  - by move=> [[]]. 
  - by exists ([fsfun m with x |-> v]).
  case: (m x == v)=> //=; constructor; last by move=> [].
  by exists m; rewrite eqxx. 
Qed.

End LTS.

Module Export Exports.
Implicit Types (A V : inhType).

Definition ltsMixin A V := 
  let S := (state A V) in
  let L := (label A V) in
  @LTS.LTS.Mixin S L _ _ _ enabledP. 
Definition ltsType A V := 
  Eval hnf in (LTSType _ _ (ltsMixin A V)).

End Exports.
End LTS.

Export LTS.Exports.


Module Export Label.
Section Label.
Context {Addr Val : inhType}.
Local Notation label := (label Addr Val).
Implicit Types (ls : {fset label}) (l : label).

Definition rf : rel label := 
  fun w r => match w, r with
  | Write x a, Read y b => (x == y) && (a == b)
  | _ , _ => false
  end.

Definition com ws r := 
  let w := odflt Bot (fset_pick ws) in
  (#|` ws | == 1) && (rf w r).

Definition cf_typ l1 l2 := 
  match (typ l1), (typ l2) with 
  | Lab.Read , Lab.Write  => true
  | Lab.Write, Lab.Read   => true
  | Lab.Write, Lab.Write  => true
  | _        , _          => false
  end.

Definition cf l1 l2 := 
  (cf_typ l1 l2) && (addr l1 == addr l2). 

Definition is_write l := 
  typ l == Lab.Write.

Definition is_read l := 
  typ l == Lab.Read.

Lemma is_writeP w :
  reflect (exists ws r, com ws r /\ w \in ws) (is_write w).
Proof. 
  apply/(equivP idP); split; rewrite /com /rf.
  - move=> isW; exists [fset w].
    move: w isW; case=> //= x v _.
    exists (Read x v); rewrite inE; split=> //=.
    by rewrite fset_pick1 cardfs1 /= !eqxx. 
  move=> /= [ws] [r] [] /andP[] /cardfs1P[w'] ->.
  rewrite fset_pick1 inE /=. 
  by move=> /[swap] /eqP<-; case: w.
Qed.

Lemma is_readP r :
  reflect (exists ws, com ws r) (is_read r).
Proof. 
  apply/(equivP idP); split; rewrite /com /rf.
  - case: r=> // x v _.
    exists [fset (Write x v)].
    by rewrite fset_pick1 cardfs1 /= !eqxx. 
  move=> [ws] /andP[] /cardfs1P[w] ->.
  rewrite fset_pick1 /=. 
  by case: w; case: r.
Qed.    

Lemma bot_nwrite : 
  ~~ is_write Bot.
Proof. done. Qed.

Lemma bot_nread : 
  ~~ is_read Bot.
Proof. done. Qed. 

End Label.

Module Export Exports.
Section Exports.
Implicit Types (A V : inhType).

Definition labMixin A V := 
  @Lab.Lab.Mixin (label A V) _ Bot com cf is_write is_read
    is_writeP is_readP bot_nwrite bot_nread.
Canonical labType A V := 
  Lab.Lab.Pack (Lab.Lab.Class (labMixin A V)).

End Exports.
End Exports.

End Label.

End SharedMem.

Export SharedMem.Exports.
Export SharedMem.LTS.Exports.
Export SharedMem.Label.Exports.
