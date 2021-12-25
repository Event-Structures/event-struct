From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq path.
From mathcomp Require Import finmap choice eqtype order zify.
From eventstruct Require Import utils wftype.

(******************************************************************************)
(* This file contains a theory of types that can be used as identifiers.      *)
(* Essentially, a type of identifiers is an infinite countable type.          *)
(*                                                                            *)
(*  identType  == interface for types which behave as identifiers.            *)
(*    \i0, \i1 == some distinguished identifiers.                             *)
(*     fresh i == allocates a fresh identifier which is guaranteed to         *)
(*                differ from i.                                              *) 
(*  nfresh i n == allocates n fresh identifier which are guaranteed to        *)
(*                differ from i.                                              *)
(* fresh_seq s == allocates a fresh identifier which is guaranteed to         *)
(*                differ from all identifiers from the list s                 *)
(*                                                                            *)
(* Elements of identType also can be converted to natural numbers and back    *)
(* from natural numbers. This conversion also induces a total well-founded    *)
(* order on identifiers.                                                      *)
(*    encode i == converts the identifier i into a natural number.            *)
(*    decode n == converts the natural number n into an identifier.           *)
(*    x <=^i y == a total well-founded order on identifiers induced           *)
(*                by the conversion to natural numbers.                       *)
(*                That is x <=^i y iff encode x <= encode y.                  *)
(*                All conventional order notations are defined with           *)
(*                the suffix _^i as well.                                     *)
(*                                                                            *)
(* This file also contains canonical instance of identType for nat.           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.
Import Order.TTheory.
Open Scope order_scope.

Declare Scope ident_scope.
Delimit Scope ident_scope with ident.

Local Open Scope ident_scope.

(* Notation for initial identifier *)
Reserved Notation "\i0" (at level 0).
Reserved Notation "\i1" (at level 0).

(* Notations for canonical order on identifiers *)
Reserved Notation "x <=^i y" (at level 70, y at next level).
Reserved Notation "x >=^i y" (at level 70, y at next level).
Reserved Notation "x <^i y" (at level 70, y at next level).
Reserved Notation "x >^i y" (at level 70, y at next level).
Reserved Notation "x <=^i y :> T" (at level 70, y at next level).
Reserved Notation "x >=^i y :> T" (at level 70, y at next level).
Reserved Notation "x <^i y :> T" (at level 70, y at next level).
Reserved Notation "x >^i y :> T" (at level 70, y at next level).
Reserved Notation "<=^i y" (at level 35).
Reserved Notation ">=^i y" (at level 35).
Reserved Notation "<^i y" (at level 35).
Reserved Notation ">^i y" (at level 35).
Reserved Notation "<=^i y :> T" (at level 35, y at next level).
Reserved Notation ">=^i y :> T" (at level 35, y at next level).
Reserved Notation "<^i y :> T" (at level 35, y at next level).
Reserved Notation ">^i y :> T" (at level 35, y at next level).
Reserved Notation "x >=<^i y" (at level 70, no associativity).
Reserved Notation ">=<^i y" (at level 35).
Reserved Notation ">=<^i y :> T" (at level 35, y at next level).
Reserved Notation "x ><^i y" (at level 70, no associativity).
Reserved Notation "><^i x" (at level 35).
Reserved Notation "><^i y :> T" (at level 35, y at next level).
Reserved Notation "x <=^i y <=^i z" (at level 70, y, z at next level).
Reserved Notation "x <^i y <=^i z" (at level 70, y, z at next level).
Reserved Notation "x <=^i y <^i z" (at level 70, y, z at next level).
Reserved Notation "x <^i y <^i z" (at level 70, y, z at next level).
Reserved Notation "x <=^i y ?= 'iff' c" (at level 70, y, c at next level,
  format "x '[hv'  <=^i  y '/'  ?=  'iff'  c ']'").
Reserved Notation "x <=^i y ?= 'iff' c :> T" (at level 70, y, c at next level,
  format "x '[hv'  <=^i  y '/'  ?=  'iff'  c  :> T ']'").
Reserved Notation "x <^i y ?<= 'if' c" (at level 70, y, c at next level,
  format "x '[hv'  <^i  y '/'  ?<=  'if'  c ']'").
Reserved Notation "x <^i y ?<= 'if' c :> T" (at level 70, y, c at next level,
  format "x '[hv'  <^i  y '/'  ?<=  'if'  c  :> T ']'").

Module Ident.
Section ClassDef.

Record mixin_of T0 (b : Countable.class_of T0)
  (T := Countable.Pack b) := Mixin {
  _ : forall n, @unpickle T n;
  _ : injective (@unpickle T)
}.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base  : Countable.class_of T;
  mixin : mixin_of base;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> Countable.class_of.

Structure type := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack :=
  fun bT b & phant_id (@Countable.class bT) b =>
  fun m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition countType := @Countable.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Countable.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Notation identType := type.
Notation IdentType T m := (@pack T _ _ id m).
Notation "[ 'identType' 'of' T 'for' cT ]" := (@clone T cT _ id)
  (at level 0, format "[ 'identType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'identType' 'of' T ]" := [identType of T for _]
  (at level 0, format "[ 'identType'  'of'  T ]") : form_scope.
End Exports.

Module Export Def.

Definition unpickle_tot {T : identType} n : @unpickle T n. 
Proof. by case: T=> ? [? []]. Defined.

Notation encode (* : T -> nat *) := (pickle).
Notation decode (* : nat -> T *) := (mk_total unpickle_tot).

Section Def.
Context {T : identType}.

Definition ident0 : T := 
  decode 0%nat.

Definition fresh : T -> T := 
  fun x => decode (1 + encode x).

Definition ident1 : T := 
  fresh ident0.

Definition nfresh : T -> nat -> seq T := 
  fun i n => traject fresh i n.

Definition ident_le : rel T := 
  fun x y => encode x <= encode y.

Definition ident_lt : rel T := 
  fun x y => encode x < encode y.

Definition ident_min : T -> T -> T := 
  fun x y => decode (minn (encode x) (encode y)).

Definition ident_max : T -> T -> T := 
  fun x y => decode (maxn (encode x) (encode y)).

End Def.
End Def. 

Prenex Implicits fresh ident_le ident_lt.

(* basic properties required by canonical instances *)
Module Export Props.
Section Props.

Context {T : identType}.
Implicit Types (x : T) (s : seq T).

Lemma unpickle_inj : 
  injective (@unpickle T).
Proof. by case: T=> ? [/= ? []]. Qed.

Lemma decode_inj : 
  injective (decode : nat -> T).
Proof. by apply /mk_total_inj /unpickle_inj. Qed.

Lemma encodeK : 
  cancel encode (decode : nat -> T). 
Proof. by apply /mk_totalK /pickleK. Qed.

Lemma decodeK : 
  cancel decode (encode : T -> nat). 
Proof. by apply/inj_can_sym; [exact/encodeK | exact/decode_inj]. Qed.

Lemma encode0 : 
  encode (ident0 : T) = 0%nat.
Proof. by rewrite /ident0; exact /decodeK. Qed.

Lemma encode1 : 
  encode (ident1 : T) = 1%nat.
Proof. by rewrite /ident1 /fresh decodeK encode0. Qed.

Lemma encode_fresh (e : T) : encode (fresh e) = (encode e).+1.
Proof. rewrite /fresh decodeK; lia. Qed.

Lemma encode_iter (e : T) n : 
  encode (iter n fresh e) = (encode e) + n.
Proof.
  elim: n=> //= [|?]; first lia.
  rewrite encode_fresh; lia.
Qed.


Lemma encode_inj : injective (@encode T).
Proof. exact/pickle_inj. Qed.


End Props.
End Props.


Module Export Order. 
Section Order. 

Context (T : identType).
Implicit Types (x y z : T).

Lemma disp : unit. 
Proof. exact: tt. Qed.

Lemma lt_def x y : (ident_lt x y) = (y != x) && (ident_le x y).
Proof. 
  rewrite /ident_lt /ident_le. 
  have ->: (y != x) = (pickle y != pickle x); last exact /lt_def. 
  case H: (y == x); first by (move: H=> /eqP->; rewrite eq_refl).
  move=> /=; apply esym.
  move: H=> /eqP /eqP /=. 
  by apply /contra_neq /pickle_inj.
Qed.

Lemma meet_def x y : ident_min x y = (if ident_lt x y then x else y).
Proof. 
  rewrite /ident_min /ident_lt /minn /Order.lt=> /=.
  rewrite (mk_totalE ident0).
  by case: ifP=> ?; rewrite pickleK /=. 
Qed.

Lemma join_def x y : ident_max x y = (if ident_lt x y then y else x).
Proof. 
  rewrite /ident_max /ident_lt /maxn /Order.lt=> /=.
  rewrite (mk_totalE ident0).
  by case: ifP=> ?; rewrite pickleK /=. 
Qed.

Lemma le_anti : antisymmetric (@ident_le T). 
Proof. 
  move=> x y /andP []; rewrite /ident_le=> ??.
  by apply /pickle_inj /anti_leq /andP. 
Qed.

Lemma le_trans : transitive (@ident_le T). 
Proof. by move=> z x y; rewrite /ident_le; apply leq_trans. Qed.

Lemma le_total : total (@ident_le T). 
Proof. by move=> x y; rewrite /ident_le; apply leq_total. Qed.

Lemma le0x x : ident_le ident0 x.
Proof. rewrite /ident_le encode0; exact /leq0n. Qed.

Lemma wfb : well_founded_bool (@ident_lt T).
Proof.
  move=> x; rewrite /ident_lt.
  rewrite -(encodeK x).
  elim/(@wfb_ind _ nat_wfType): (encode x).
  constructor=> y.
  rewrite decodeK -{2}(encodeK y).
  by apply /X.
Qed.  

Definition mixin :=
  LeOrderMixin lt_def meet_def join_def le_anti le_trans le_total.

End Order.

Module Export Exports.

Implicit Types (T : identType). 

Canonical porderType T := POrderType disp T (@Order.mixin T).
Canonical latticeType T := LatticeType T (@Order.mixin T).
Canonical bLatticeType T := BLatticeType T (BottomMixin (@Order.le0x T)).
Canonical distrLatticeType T := DistrLatticeType T (@Order.mixin T).
Canonical bDistrLatticeType T := [bDistrLatticeType of T].
Canonical orderType T := OrderType T (@Order.mixin T).

Canonical wfType T := 
  let wf_mixin := @WellFounded.Mixin T 
     (Order.POrder.class (porderType T)) (@Order.wfb T) 
  in WfType disp T wf_mixin.

Coercion porderType : type >-> Order.POrder.type.
Coercion latticeType : type >-> Order.Lattice.type.
Coercion bLatticeType : type >-> Order.BLattice.type.
Coercion distrLatticeType : type >-> Order.DistrLattice.type.
Coercion bDistrLatticeType : type >-> Order.BDistrLattice.type.
Coercion wfType : type >-> WellFounded.type.
(* Coercion orderType : type >-> Order.TOrder.type. *)

End Exports.

End Order.

Module Export Syntax. 

Notation "'\i0'" := (ident0) : ident_scope.
Notation "'\i1'" := (ident1) : ident_scope.

Notation ident_le := (@Order.le (Order.disp) _).
Notation ident_lt := (@Order.lt (Order.disp) _).
Notation ident_comparable := (@Order.comparable (Order.disp) _).
Notation ident_ge := (@Order.ge (Order.disp) _).
Notation ident_gt := (@Order.gt (Order.disp) _).
Notation ident_leif := (@Order.leif (Order.disp) _).
Notation ident_lteif := (@Order.lteif (Order.disp) _).
Notation ident_max := (@Order.max (Order.disp) _).
Notation ident_min := (@Order.min (Order.disp) _).
Notation ident_meet := (@Order.meet (Order.disp) _).
Notation ident_join := (@Order.join (Order.disp) _).
Notation ident_bottom := (@Order.bottom (Order.disp) _).
Notation ident_top := (@Order.top (Order.disp) _).

Notation "<=^i%O" := ident_le : fun_scope.
Notation ">=^i%O" := ident_ge : fun_scope.
Notation "<^i%O" := ident_lt : fun_scope.
Notation ">^i%O" := ident_gt : fun_scope.
Notation "<?=^i%O" := ident_leif : fun_scope.
Notation "<?<=^i%O" := ident_lteif : fun_scope.
Notation ">=<^i%O" := ident_comparable : fun_scope.
Notation "><^i%O" := (fun x y => ~~ ident_comparable x y) : fun_scope.

Notation "<=^i y" := (>=^i%O y) : order_scope.
Notation "<=^i y :> T" := (<=^i (y : T)) (only parsing) : order_scope.
Notation ">=^i y" := (<=^i%O y) : order_scope.
Notation ">=^i y :> T" := (>=^i (y : T)) (only parsing) : order_scope.

Notation "<^i y" := (>^i%O y) : order_scope.
Notation "<^i y :> T" := (<^i (y : T)) (only parsing) : order_scope.
Notation ">^i y" := (<^i%O y) : order_scope.
Notation ">^i y :> T" := (>^i (y : T)) (only parsing) : order_scope.

Notation "x <=^i y" := (<=^i%O x y) : order_scope.
Notation "x <=^i y :> T" := ((x : T) <=^i (y : T)) (only parsing) : order_scope.
Notation "x >=^i y" := (y <=^i x) (only parsing) : order_scope.
Notation "x >=^i y :> T" := ((x : T) >=^i (y : T)) (only parsing) : order_scope.

Notation "x <^i y" := (<^i%O x y) : order_scope.
Notation "x <^i y :> T" := ((x : T) <^i (y : T)) (only parsing) : order_scope.
Notation "x >^i y" := (y <^i x) (only parsing) : order_scope.
Notation "x >^i y :> T" := ((x : T) >^i (y : T)) (only parsing) : order_scope.

Notation "x <=^i y <=^i z" := ((x <=^i y) && (y <=^i z)) : order_scope.
Notation "x <^i y <=^i z" := ((x <^i y) && (y <=^i z)) : order_scope.
Notation "x <=^i y <^i z" := ((x <=^i y) && (y <^i z)) : order_scope.
Notation "x <^i y <^i z" := ((x <^i y) && (y <^i z)) : order_scope.

Notation "x <=^i y ?= 'iff' C" := (<?=^i%O x y C) : order_scope.
Notation "x <=^i y ?= 'iff' C :> T" := ((x : T) <=^i (y : T) ?= iff C)
  (only parsing) : order_scope.

Notation "x <^i y ?<= 'if' C" := (<?<=^i%O x y C) : order_scope.
Notation "x <^i y ?<= 'if' C :> T" := ((x : T) <^i (y : T) ?<= if C)
  (only parsing) : order_scope.

Notation ">=<^i x" := (>=<^i%O x) : order_scope.
Notation ">=<^i y :> T" := (>=<^i (y : T)) (only parsing) : order_scope.
Notation "x >=<^i y" := (>=<^i%O x y) : order_scope.

Notation "><^i y" := [pred x | ~~ ident_comparable x y] : order_scope.
Notation "><^i y :> T" := (><^i (y : T)) (only parsing) : order_scope.
Notation "x ><^i y" := (~~ (><^i%O x y)) : order_scope.

End Syntax.

Module Export Theory.
Section Theory.


Lemma foldr_monoid {S : Type} {f : S -> S -> S} {n s1 s2}: 
  associative f ->
  (forall a, f n a = a) ->
  (forall a, f a n = a) ->
  f (foldr f n s1) (foldr f n s2) =
  foldr f n (s1 ++ s2).
Proof. by move=> A L R; elim: s1=> //= ??; rewrite -A=>->. Qed.

Context {T : identType}.
Implicit Types (x : T) (s : seq T).

Lemma fresh_lt x : 
  x <^i fresh x.
Proof. 
  rewrite /fresh /ident_lt /= /Def.ident_lt decodeK. 
  exact /ltnSn.
Qed.

Lemma fresh_mon x y : x <=^i y = (fresh x <=^i fresh y).
Proof.
  rewrite ?/(_ <=^i _) /= /Def.ident_le /fresh ?decodeK; lia.
Qed.

Lemma fresh_inj : 
  injective (@fresh T).
Proof. by rewrite /fresh=> x y /decode_inj [] /pickle_inj. Qed.

Lemma size_nfresh x n : 
  size (nfresh x n) = n.
Proof. by rewrite /nfresh size_traject. Qed.

Lemma nth_nfresh x n i : 
  i < n -> nth x (nfresh x n) i = iter i fresh x.
Proof. by rewrite /nfresh=> ?; apply /nth_traject. Qed.

Lemma nfresh_head x y n : 
  head x (nfresh y n) = if n == 0 then x else y.
Proof. by case: n=> //=. Qed.

Lemma nfresh_sorted x n : 
  sorted (<%O) (nfresh x n).
Proof. 
  rewrite /nfresh; case: n=> //= n.
  apply /sub_path; last exact/fpath_traject.
  move=> ?? /= /eqP <-; exact/fresh_lt.
Qed.  

Lemma nfreshS x n : 
  nfresh x n.+1 = x :: nfresh (fresh x) n.
Proof. by rewrite /nfresh; exact/trajectS. Qed.

Lemma nfreshSr x n : 
  nfresh x n.+1 = rcons (nfresh x n) (iter n fresh x).
Proof. by rewrite /nfresh; exact/trajectSr. Qed.

Lemma in_nfresh x n y : 
  y \in nfresh x n = (encode x <= encode y < n + encode x)%N.
Proof.
  elim: n x=> //= [?|?/[swap] ?]; rewrite ?(inE, in_nil); first lia.
  move=>->; rewrite encode_fresh -(inj_eq encode_inj); lia.
Qed.

Import Order.

Definition fresh_seq : seq T -> T := fun t => 
  fresh (foldr Order.max \i0 t).

Lemma fresh_seq_nil : 
  fresh_seq [::] = (\i1 : T).
Proof. by rewrite /fresh_seq /=. Qed.

Lemma fresh_seq0 s : 
  \i0 <^i fresh_seq s.
Proof. by rewrite /fresh_seq /ident0 /ident_lt /= /Def.ident_lt !decodeK. Qed.

Lemma i0_min {x} : \i0 <=^i x.
Proof. by rewrite /(_ <=^i _)/= /Def.ident_le encode0. Qed.

Hint Resolve i0_min : core.

Lemma maxx0 x : Order.max x \i0 = x.
Proof. exact/max_idPl. Qed.

Lemma max0x x : Order.max \i0 x = x.
Proof. exact/max_idPr. Qed.

Lemma max_fresh x y: 
  Order.max (fresh x) (fresh y) = fresh (Order.max x y).
Proof.
  rewrite ?maxEle -fresh_mon; by case: ifP.
Qed.


Lemma fresh_seq_mem x s : 
  x \in s -> x <^i fresh_seq s.
Proof. 
  rewrite /fresh_seq.
  elim: s=> [|y {}s IH] => //=.
  rewrite maxElt ?inE; case: ifP=> /[swap]/orP[/eqP<-|/IH] //.
  - by move/lt_trans/(_ (fresh_lt _)).
  - by move: (fresh_lt x).
  rewrite (ltNge y)=> /[swap]/negbT/[! negbK].
  by rewrite fresh_mon=> /lt_le_trans/[apply].
Qed.

Lemma fresh_seq_nmem s : fresh_seq s \notin s.
Proof. by apply/memPn => x /fresh_seq_mem; rewrite lt_neqAle=> /andP[]. Qed.

(* Lemma fresh_seq_nfresh x n : 
  0 < n -> fresh_seq (nfresh x n) = iter n fresh x.
Proof. 
  rewrite /fresh_seq foldl_maxn_sorted; last first.
  - rewrite sorted_map; apply /sub_sorted /nfresh_sorted.
    rewrite /ident_lt /= /Def.ident_lt=> {}x y /=; exact /ltW.
  have {2}->: 0%nat = @encode T \i0 by apply/esym/encode0.
  rewrite last_map; case: n=> [|{}n].
  - by rewrite encode0=> /=. 
  by rewrite nfreshSr last_rcons iterS /fresh.
Qed. *)

Lemma mem_le_max s x: 
  x \in s -> x <= foldr ident_max \i0 s.
Proof.
  elim: s=> //= a l IH; rewrite ?inE le_maxr=> /orP[/eqP->|/IH->] //.
  by rewrite lexx.
Qed. 

Lemma fresh_seq_subset s1 s2: {subset s1 <= s2} -> fresh_seq s1 <=^i fresh_seq s2.
Proof.
  rewrite /fresh_seq -fresh_mon; elim: s1 s2=> //=a s1 IH s2 s.
  rewrite le_maxl; apply/andP; split.
  - exact/mem_le_max/(s a)/mem_head.
  by apply/IH=> ? I; apply/s; rewrite inE I orbT.
Qed.

Lemma fresh_seq_eq s1 s2: s1 =i s2 -> fresh_seq s1 = fresh_seq s2.
Proof.
  by move=> I; apply/le_anti/andP; split; apply/fresh_seq_subset=> ? /[! I].
Qed.

Lemma fresh_seqU (s1 s2 : {fset T}): 
  fresh_seq (s1 `|` s2)%fset = Order.max (fresh_seq s1) (fresh_seq s2).
Proof.
  have->: Order.max (fresh_seq s1) (fresh_seq s2) = fresh_seq (s1 ++ s2).
  - apply/eqP; rewrite max_fresh /fresh_seq (inj_eq fresh_inj).
    exact/eqP/(foldr_monoid maxA max0x maxx0).
  have/andP/(le_anti) //: 
    ((fresh_seq (s1 `|` s2)%fset <=^i fresh_seq (s1 ++ s2)) /\ 
    (fresh_seq (s1 ++ s2) <=^i fresh_seq (s1 `|` s2)%fset)).
  split; apply/fresh_seq_subset=> ?; by rewrite ?inE mem_cat.
Qed.

Lemma fresh_seq_add x (s : {fset T}) : 
  fresh_seq (x |` s)%fset = Order.max (fresh x) (fresh_seq s).
Proof.
  rewrite fresh_seqU. 
  under (@fresh_seq_eq _ [:: x]) do rewrite ?inE //.
  by rewrite {1}/fresh_seq /= maxx0.
Qed.


End Theory.
End Theory.

End Ident.

Export Ident.Exports.
Export Ident.Order.Exports.
Export Ident.Def.
Export Ident.Props.
Export Ident.Syntax.
Export Ident.Theory.

(* Context {T : identType}. *)
(* Variable (x y : T). *)
(* Check (x <=^i y : bool). *)

Lemma nat_unpickle_tot (n : nat) : (unpickle n : option nat).
Proof. done. Qed.

Lemma nat_unpickle_inj : injective (unpickle : nat -> option nat).
Proof. exact/Some_inj. Qed.

Definition nat_identMixin :=
  @Ident.Mixin nat (Countable.class nat_countType) 
               nat_unpickle_tot nat_unpickle_inj.

Canonical nat_identType :=
  Eval hnf in IdentType nat nat_identMixin.
