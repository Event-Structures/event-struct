From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat. 
From mathcomp Require Import seq choice eqtype order.
From eventstruct Require Import utils ssrnatlia wftype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.
Open Scope order_scope.

(* Notations for canonical order on countable types *)
Reserved Notation "x <=^n y" (at level 70, y at next level).
Reserved Notation "x >=^n y" (at level 70, y at next level).
Reserved Notation "x <^n y" (at level 70, y at next level).
Reserved Notation "x >^n y" (at level 70, y at next level).
Reserved Notation "x <=^n y :> T" (at level 70, y at next level).
Reserved Notation "x >=^n y :> T" (at level 70, y at next level).
Reserved Notation "x <^n y :> T" (at level 70, y at next level).
Reserved Notation "x >^n y :> T" (at level 70, y at next level).
Reserved Notation "<=^n y" (at level 35).
Reserved Notation ">=^n y" (at level 35).
Reserved Notation "<^n y" (at level 35).
Reserved Notation ">^n y" (at level 35).
Reserved Notation "<=^n y :> T" (at level 35, y at next level).
Reserved Notation ">=^n y :> T" (at level 35, y at next level).
Reserved Notation "<^n y :> T" (at level 35, y at next level).
Reserved Notation ">^n y :> T" (at level 35, y at next level).
Reserved Notation "x >=<^n y" (at level 70, no associativity).
Reserved Notation ">=<^n y" (at level 35).
Reserved Notation ">=<^n y :> T" (at level 35, y at next level).
Reserved Notation "x ><^n y" (at level 70, no associativity).
Reserved Notation "><^n x" (at level 35).
Reserved Notation "><^n y :> T" (at level 35, y at next level).
Reserved Notation "x <=^n y <=^n z" (at level 70, y, z at next level).
Reserved Notation "x <^n y <=^n z" (at level 70, y, z at next level).
Reserved Notation "x <=^n y <^n z" (at level 70, y, z at next level).
Reserved Notation "x <^n y <^n z" (at level 70, y, z at next level).
Reserved Notation "x <=^n y ?= 'iff' c" (at level 70, y, c at next level,
  format "x '[hv'  <=^n  y '/'  ?=  'iff'  c ']'").
Reserved Notation "x <=^n y ?= 'iff' c :> T" (at level 70, y, c at next level,
  format "x '[hv'  <=^n  y '/'  ?=  'iff'  c  :> T ']'").
Reserved Notation "x <^n y ?<= 'if' c" (at level 70, y, c at next level,
  format "x '[hv'  <^n  y '/'  ?<=  'if'  c ']'").
Reserved Notation "x <^n y ?<= 'if' c :> T" (at level 70, y, c at next level,
  format "x '[hv'  <^n  y '/'  ?<=  'if'  c  :> T ']'").

Section Utils. 
Context {T : countType}.

Lemma pickle_inj : injective (@pickle T).
Proof. apply /pcan_inj /choice.pickleK. Qed.

End Utils.

Module Order. 
Section Order. 

Context {T : countType}.
Implicit Types (x y z : T).

Definition le : rel T := 
  fun x y => pickle x <= pickle y.

Definition lt : rel T := 
  fun x y => pickle x < pickle y.

Definition min : T -> T -> T := 
  fun x y => odflt x (unpickle (minn (pickle x) (pickle y))).

Definition max : T -> T -> T := 
  fun x y => odflt x (unpickle (maxn (pickle x) (pickle y))).

Lemma disp : unit. 
Proof. exact: tt. Qed.

Lemma lt_def x y : (lt x y) = (y != x) && (le x y).
Proof. 
  rewrite /lt /le. 
  have ->: (y != x) = (pickle y != pickle x); last exact /lt_def. 
  case H: (y == x); first by (move: H=> /eqP->; rewrite eq_refl).
  move=> /=; apply esym.
  move: H=> /eqP /eqP /=. 
  by apply /contra_neq /pickle_inj.
Qed.

Lemma meet_def x y : min x y = (if lt x y then x else y).
Proof. 
  rewrite /min /lt /minn /order.Order.lt => /=.
  by case: ifP=> ?; rewrite pickleK /=. 
Qed.

Lemma join_def x y : max x y = (if lt x y then y else x).
Proof. 
  rewrite /max /lt /maxn /order.Order.lt=> /=.
  by case: ifP=> ?; rewrite pickleK /=. 
Qed.

Lemma le_anti : antisymmetric le. 
Proof. 
  move=> x y /andP []; rewrite /le=> ??.
  by apply /pickle_inj /anti_leq /andP. 
Qed.

Lemma le_trans : transitive le. 
Proof. by move=> z x y; rewrite /le; apply leq_trans. Qed.

Lemma le_total : total le. 
Proof. by move=> x y; rewrite /le; apply leq_total. Qed.

Lemma wfb : well_founded_bool lt.
Proof.
  move=> x; rewrite /lt.
  rewrite -(odflt_pcancel x x pickleK).
  remember (pickle x) as n; move: x Heqn. 
  elim/(@wfb_ind _ nat_wfType): n.
  move=> n IH x Heq; rewrite Heq.
  constructor=> y. 
  rewrite pickleK=> /= H.
  rewrite -(odflt_pcancel y y pickleK).
  by apply /IH; rewrite ?Heq. 
Qed.  

Definition mixin :=
  LeOrderMixin lt_def meet_def join_def le_anti le_trans le_total.

End Order.

Prenex Implicits le lt.

Definition type (T : Type) := T.

Module Export Exports.
Implicit Types (T : countType). 

Notation "T ^n" := (type T) (at level 2, format "T ^n").

Canonical porderType T := POrderType disp T^n (@mixin T).
Canonical latticeType T := LatticeType T^n (@mixin T).
Canonical distrLatticeType T := DistrLatticeType T^n (@mixin T).
Canonical wfType T := 
  let wf_mixin := @WellFounded.Mixin T 
     (Order.POrder.class (porderType T)) (@wfb T) 
  in WellFounded.Pack disp (WellFounded.Class wf_mixin).

Coercion porderType : countType >-> Order.POrder.type.
Coercion latticeType : countType >-> Order.Lattice.type.
Coercion distrLatticeType : countType >-> Order.DistrLattice.type.
Coercion wfType : countType >-> WellFounded.type.

End Exports.

Module Export Syntax. 

Notation le := (@order.Order.le disp _).
Notation lt := (@order.Order.lt disp _).
Notation comparable := (@order.Order.comparable disp _).
Notation ge := (@order.Order.ge disp _).
Notation gt := (@order.Order.gt disp _).
Notation leif := (@order.Order.leif disp _).
Notation lteif := (@order.Order.lteif disp _).
Notation max := (@order.Order.max disp _).
Notation min := (@order.Order.min disp _).
Notation meet := (@order.Order.meet disp _).
Notation join := (@order.Order.join disp _).
Notation bottom := (@order.Order.bottom disp _).
Notation top := (@order.Order.top disp _).

Notation "<=^n%O" := le : fun_scope.
Notation ">=^n%O" := ge : fun_scope.
Notation "<^n%O" := lt : fun_scope.
Notation ">^n%O" := gt : fun_scope.
Notation "<?=^n%O" := leif : fun_scope.
Notation "<?<=^n%O" := lteif : fun_scope.
Notation ">=<^n%O" := comparable : fun_scope.
Notation "><^n%O" := (fun x y => ~~ comparable x y) : fun_scope.

Notation "<=^n y" := (>=^n%O y) : order_scope.
Notation "<=^n y :> T" := (<=^n (y : T)) (only parsing) : order_scope.
Notation ">=^n y" := (<=^n%O y) : order_scope.
Notation ">=^n y :> T" := (>=^n (y : T)) (only parsing) : order_scope.

Notation "<^n y" := (>^n%O y) : order_scope.
Notation "<^n y :> T" := (<^n (y : T)) (only parsing) : order_scope.
Notation ">^n y" := (<^n%O y) : order_scope.
Notation ">^n y :> T" := (>^n (y : T)) (only parsing) : order_scope.

Notation "x <=^n y" := (<=^n%O x y) : order_scope.
Notation "x <=^n y :> T" := ((x : T) <=^n (y : T)) (only parsing) : order_scope.
Notation "x >=^n y" := (y <=^n x) (only parsing) : order_scope.
Notation "x >=^n y :> T" := ((x : T) >=^n (y : T)) (only parsing) : order_scope.

Notation "x <^n y" := (<^n%O x y) : order_scope.
Notation "x <^n y :> T" := ((x : T) <^n (y : T)) (only parsing) : order_scope.
Notation "x >^n y" := (y <^n x) (only parsing) : order_scope.
Notation "x >^n y :> T" := ((x : T) >^n (y : T)) (only parsing) : order_scope.

Notation "x <=^n y <=^n z" := ((x <=^n y) && (y <=^n z)) : order_scope.
Notation "x <^n y <=^n z" := ((x <^n y) && (y <=^n z)) : order_scope.
Notation "x <=^n y <^n z" := ((x <=^n y) && (y <^n z)) : order_scope.
Notation "x <^n y <^n z" := ((x <^n y) && (y <^n z)) : order_scope.

Notation "x <=^n y ?= 'iff' C" := (<?=^n%O x y C) : order_scope.
Notation "x <=^n y ?= 'iff' C :> T" := ((x : T) <=^n (y : T) ?= iff C)
  (only parsing) : order_scope.

Notation "x <^n y ?<= 'if' C" := (<?<=^n%O x y C) : order_scope.
Notation "x <^n y ?<= 'if' C :> T" := ((x : T) <^n (y : T) ?<= if C)
  (only parsing) : order_scope.

Notation ">=<^n x" := (>=<^n%O x) : order_scope.
Notation ">=<^n y :> T" := (>=<^n (y : T)) (only parsing) : order_scope.
Notation "x >=<^n y" := (>=<^n%O x y) : order_scope.

Notation "><^n y" := [pred x | ~~ comparable x y] : order_scope.
Notation "><^n y :> T" := (><^n (y : T)) (only parsing) : order_scope.
Notation "x ><^n y" := (~~ (><^n%O x y)) : order_scope.

End Syntax.

End Order.

Export Order.Exports.
Export Order.Syntax.
