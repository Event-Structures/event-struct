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
Context {dA dV : unit} {Addr : inhType dA} {Val : inhType dV}.

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

Arguments state {_ _} _ _ .
Arguments label {_ _} _ _ .

Section Encode. 
Context {dA dV : unit} {Addr : inhType dA} {Val : inhType dV}.

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
Section Exports.
Context {dA dV : unit} {A : inhType dA} {V : inhType dV}.

Definition label_eqMixin := 
  CanEqMixin (@enc_dec_labK _ _ A V).
Canonical label_eqType := 
  Eval hnf in EqType _ label_eqMixin.

Definition label_choiceMixin := 
  CanChoiceMixin (@enc_dec_labK _ _ A V).
Canonical label_choiceType := 
  Eval hnf in ChoiceType _ label_choiceMixin.

End Exports.
End Exports.


Module Export LTS.
Section LTS.
Context {dA dV : unit} {Addr : inhType dA} {Val : inhType dV}.
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
Section Exports.
Context {dA dV : unit} {A : inhType dA} {V : inhType dV}.

Definition ltsMixin := 
  let S := (state A V) in
  let L := (label A V) in
  @LTS.LTS.Mixin S L _ _ _ enabledP. 
Definition ltsType := 
  Eval hnf in (LTSType _ _ ltsMixin).

End Exports.
End Exports. 

End LTS.

Export LTS.Exports.


Module Export Label.
Section Label.
Context {dA dV : unit} {Addr : inhType dA} {Val : inhType dV}.
Local Notation label := (label Addr Val).
Implicit Types (ls : {fset label}) (l : label).

Definition rf : rel label := 
  fun w r => match w, r with
  | Write x a, Read y b => (x == y) && (a == b)
  | _ , _ => false
  end.

Definition com ws r := 
  let w := odflt Bot (fpick ws) in
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
    by rewrite fpick1 cardfs1 /= !eqxx. 
  move=> /= [ws] [r] [] /andP[] /cardfs1P[w'] ->.
  rewrite fpick1 inE /=. 
  by move=> /[swap] /eqP<-; case: w.
Qed.

Lemma is_readP r :
  reflect (exists ws, com ws r) (is_read r).
Proof. 
  apply/(equivP idP); split; rewrite /com /rf.
  - case: r=> // x v _.
    exists [fset (Write x v)].
    by rewrite fpick1 cardfs1 /= !eqxx. 
  move=> [ws] /andP[] /cardfs1P[w] ->.
  rewrite fpick1 /=. 
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
Context {dA dV : unit} {A : inhType dA} {V : inhType dV}.

Definition inhMixin := @Inhabited.Mixin (label A V) _ Bot. 
Canonical inhType := Eval hnf in InhType (label A V) Bottom.disp inhMixin. 

Definition labMixin := 
  @Lab.Lab.Mixin (label A V) _ com cf is_write is_read
    is_writeP is_readP bot_nwrite bot_nread.
Canonical labType := 
  Lab.Lab.Pack (Lab.Lab.Class labMixin).

End Exports.
End Exports.

End Label.

End SharedMem.

Export SharedMem.Exports.
Export SharedMem.LTS.Exports.
Export SharedMem.Label.Exports.
