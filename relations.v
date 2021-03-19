From Coq Require Import Relations Relation_Operators.
From RelationAlgebra Require Import lattice monoid rel kat_tac.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype seq order choice.
From mathcomp Require Import finmap fingraph fintype finfun ssrnat path.
From Equations Require Import Equations.
From event_struct Require Import utilities wftype.

(******************************************************************************)
(* Auxiliary definitions and lemmas about binary decidable relations.         *)
(*                                                                            *)
(*   sfrel f      == a relation corresponding to non-deterministic function   *)
(*                   (i.e. list-valued function). A generalization of frel.   *)
(*                   Given a function f, sfrel denotes a relation consisting  *)
(*                   of pairs <x, y>, s.t. x \in f y                          *)
(*                   TODO: currently, the direction of the relation is        *)
(*                   reversed compared to frel, we'll fix that later.         *)
(*   strictify f  == given a non-deterministic function, removes all the      *)
(*                   elements equal to the argument of the function.          *)
(*                   It can be used to obtain a strict (i.e. irreflexive)     *)
(*                   relation corresponding to f.                             *)
(*   suffix f     == given a well-founded function f and an element x,        *)
(*                   returns a strict suffix of x, i.e. a set { y | x R y }   *)
(*                   where R ::= sfrel f.                                     *)
(*   wsuffix f    == a weak (reflexive) suffix, i.e. a set { y | x R? y }     *)
(*   t_closure f  == given a well-founded function f returns its              *)
(*                   transitive closure as a decidable relation.              *)
(*                   t_closure f ≡ (sfrel f)^+                                *)
(*   rt_closure f == given a well-founded function f returns its              *)       
(*                   reflexive-transitive closure as a decidable relation,    *)
(*                   t_closure f ≡ (sfrel f)^*                                *)
(******************************************************************************)


Set Implicit Arguments.
Unset Printing Implicit Defensive.
Set Equations Transparent.

Import Order.LTheory.
Local Open Scope order_scope.
Local Open Scope ra_terms.

Definition sfrel {T : eqType} (f : T -> seq T) : rel T :=
  [rel a b | a \in f b].

Section Strictify.

Context {T : eqType}.
Implicit Type (f : T -> seq T).

Definition strictify f : T -> seq T :=
  fun x => filter^~ (f x) (fun y => y != x).

Lemma strictify_weq f :
  sfrel (strictify f) ≡ (sfrel f \ eq_op).
Proof. 
  move=> x y; rewrite /sfrel /strictify /=.
  by rewrite mem_filter andbC.
Qed.

Lemma strictify_leq f : 
  sfrel (strictify f) ≦ sfrel f.
Proof. by rewrite strictify_weq; lattice. Qed.

End Strictify. 

Section WfRTClosure.

Context {disp : unit} {T : wfType disp}.

Variable (f : T -> seq T).

(* Hypothesis descend : forall x y, y \in f x -> y < x. *)
Hypothesis descend : sfrel f ≦ (<%O).

(* A hack to get around a bug in Equations 
 * (see https://github.com/mattam82/Coq-Equations/issues/241).
 * In short, we cannot express this function directly in Equations' syntax
 * (we can do it by adding `noind` specifier, but then we cannot use `funelim`).
 * Thus we have to "tie a recursive knot" manually. 
 *)
Definition suffix_aux (x : T) (rec : forall y : T, y < x -> seq T) := 
  let ys := f x in 
  let ps := flatten (map^~ (seq_in ys) (fun y => 
    rec (val y) (descend _ _ (valP y))
  )) 
  in ys ++ ps.

(* strict suffix of an element `x`, i.e. a set { y | x R y } *)
Equations suffix (x : T) : seq T by wf x (<%O : rel T) := 
  suffix x := suffix_aux x suffix.

(* weak suffix of an element `x`, i.e. a set { y | x R? y } *)
Definition wsuffix (x : T) : seq T :=
  x :: suffix x.

(* decidable transitive closure *)
Definition t_closure : rel T := 
  fun x y => x \in suffix y.

(* decidable reflexive-transitive closure *)
Definition rt_closure : rel T := 
  fun x y => x \in wsuffix y. 

(* ************************************************************************** *)
(*       THEORY                                                               *)
(* ************************************************************************** *)

Lemma t_closure_n1P x y : 
  reflect (clos_trans_n1 T (sfrel f) x y) (t_closure x y).
Proof.
  rewrite /t_closure. funelim (suffix y)=> /=. 
  apply /(iffP idP); rewrite mem_cat /sfrel /=.
  { move=> /orP[|/flatten_mapP[z]] //; first exact: tn1_step.
    move=> S /X H; apply: tn1_trans (valP z) _.
    by apply: H=> //=; apply: descend (valP z). }
  move: X=> /[swap] [[?->//|y ? /[dup] ? L /[swap]]].
  move=> /[apply] H; apply/orP; right; apply/flatten_mapP.
  eexists; first by apply: seq_in_mem L.
  by apply /H=> //=; apply: descend.
Qed.

Lemma t_closureP x y :
  reflect (clos_trans T (sfrel f) x y) (t_closure x y).
Proof.
  apply /(equivP (t_closure_n1P x y)).
  symmetry; exact: clos_trans_tn1_iff.
Qed.

Lemma clos_trans_lt : 
  clos_trans T (sfrel f) ≦ (<%O : rel T).
Proof. 
  move=> ??; rewrite/sfrel /=.
  elim=> [y z /descend | x y z _ ] //=.
  move=> /[swap] _; exact: lt_trans.
Qed.

Lemma t_closure_lt : t_closure ≦ (<%O : rel T).
Proof. by move=> x y /t_closureP /clos_trans_lt. Qed.

Lemma t_closure_antisym : antisymmetric t_closure.
Proof.
  move=> x y /andP[] /t_closure_lt ? /t_closure_lt ?. 
  by apply /eqP; rewrite eq_le !ltW.
Qed.

Lemma t_closure_trans : transitive t_closure.
Proof.
  move=> y x z /t_closureP ? /t_closureP ?.
  apply /t_closureP /t_trans; eauto. 
Qed.

Lemma rt_closureP x y :
  reflect (clos_refl_trans T (sfrel f) x y) (rt_closure x y).
Proof.
  apply /equivP; last first.
  { rewrite clos_refl_transE clos_reflE. 
    apply or_iff_compat_l; symmetry.
    apply rwP; exact: t_closureP. }
  rewrite /t_closure /rt_closure /wsuffix in_cons.
  by apply predU1P.
Qed.

Lemma rt_closureE : rt_closure ≡ eq_op ⊔ t_closure.
Proof. 
  move=> x y /=; rewrite /rt_closure /t_closure. 
  by rewrite /wsuffix in_cons eq_sym.
Qed.

Lemma rt_closure_le : rt_closure ≦ (<=%O : rel T).
Proof.
  rewrite rt_closureE.
  move=> x y /orP[/eqP<-//|].
  move=> /t_closure_lt; exact: ltW.
Qed.

Lemma rt_closure_refl x : rt_closure x x.
Proof. exact: mem_head. Qed.

Lemma rt_closure_antisym : antisymmetric rt_closure.
Proof.
  move=> x y /andP[]. 
  move=> /rt_closure_le /= xy /rt_closure_le /= yx. 
  by apply /eqP; rewrite eq_le xy yx. 
Qed.

Lemma rt_closure_trans : transitive rt_closure.
Proof.
  move=> y x z /rt_closureP xy /rt_closureP ?.
  by apply/rt_closureP; apply: rt_trans xy _.
Qed.

End WfRTClosure.

Section Acyclic.

Open Scope fset_scope.

Variables (T : choiceType) (f : {fsfun T -> seq T with [::]}).

Notation F := (finsupp f `|` [fset t | k in finsupp f, t in f k]).
Notation n := (#|`F|).

Lemma memF {x y}: y \in f x -> y \in F.
Proof.
  case: (boolP (x \in finsupp f))=> [*|/fsfun_dflt->//].
  rewrite in_fsetU; apply/orP; right; rewrite  -[y]/((fun=> id) x y).
  exact/in_imfset2.
Qed.

Definition hack_f : F -> seq F := 
  fun x => [seq [` memF (valP p)] | p <- seq_in (f (fsval x))].

Fixpoint fdfs n v x :=
  if x \in v then v else
  if n is n'.+1 then foldl (fdfs n') (x :: v) (f x) else v.

Lemma l (v : seq F) x: x \in v = (fsval x \in [seq fsval x | x <- v]).
Proof.
Admitted.

Lemma fdfsE n v x: 
  [seq fsval x | x <- dfs hack_f n v x] =i fdfs n [seq fsval x | x <- v] (fsval x).
Proof.
  elim n=> y //=; first by (do ?case: ifP).
  (do ? case: ifP=> //)=> E; rewrite l ?E // => _.
Admitted.

Inductive fdfs_path x y : Prop :=
  DfsPath p of path (sfrel f) x p & y = last x p.

Lemma fdfsP x y: 
  reflect (fdfs_path x y) (y \in fdfs #|`F| [::] x).
Proof.
  case L : (x \in F).
  case L' : (y \in F).
  - rewrite -[x]/(fsval [` L]) -[[::]]/([seq fsval x | x <- [::] : seq F]) -fdfsE.
    - rewrite -[y]/(fsval [` L']) -l; apply/(equivP (dfs_pathP _ _ _ _))=> //.
Admitted.

Definition fsuffix x := fdfs (#|` F|) [::] x.

Definition acyclic x := x \notin fsuffix x.

Theorem acyclicP: 
  reflect 
  (forall x, ~ (clos_trans T (sfrel f) x x)) 
  [forall x : F, acyclic (fsval x)].
Admitted.

End Acyclic.

