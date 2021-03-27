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

Module WfClosure.

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

End WfClosure.

Module FinClosure.

Section FinRTClosure.

Open Scope fset_scope.

Variables (T : choiceType) (f : {fsfun T -> seq T with [::]}).

Definition F := (finsupp f `|` [fset t | k in finsupp f, t in f k]).
Notation n := (#|`F|.+1).

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

Definition equiv (x : T) (y : F) := x == fsval y.

Definition equivs (xs : seq T) (ys : seq F) := 
  all2 equiv xs ys.

Lemma equivsP xs {ys} : 
  reflect (xs = [seq fsval y | y <- ys]) (equivs xs ys).
Proof.
  apply/(iffP idP)=> [|->]. 
  - by elim: xs ys=> [[]//|?? IHxs []//= ?? /andP[/eqP -> /IHxs->]]. 
  elim: ys=> //= ?? ->; by rewrite /equiv eq_refl.
Qed.

Lemma equivs_mem {v v' x}: equivs v v' -> (fsval x) \in v = (x \in v').
Proof.
  elim: v v'=> [[]//|?? IHv []//= ? l /andP[+ /IHv]].
  rewrite ?inE=> /eqP->->; by rewrite val_eqE.
Qed.

Lemma equivs_hack_f x: equivs (f (fsval x)) (hack_f x).
Proof.
  by apply/equivsP; rewrite -map_comp -{1}(val_seq_in (f _)) -eq_in_map.
Qed.

Lemma path_memF {x p y}: 
  path (fun x : T => (sfrel f)^~ x) x p ->
  y \in p -> y \in F.
Proof.
  elim: p x=> //= ?? IHp ? /andP[/memF ? /IHp ?]. 
  by rewrite inE=> /orP[/eqP->|].
Qed.

Lemma fdfsE {v v' n} {x : F} :
  equivs v v' ->
  equivs (fdfs n v (fsval x)) (dfs hack_f n v' x).
Proof.
  elim: n v v' x=> n IHn v v' //=; first by (do ?case: ifP).
  move=> x E; rewrite (@equivs_mem v v') // /hack_f; case: ifP=> // ?.
  apply/(rfoldl equivs equiv); first by rewrite /= /equiv eq_refl. 
  - move=> ????? /eqP ->; exact/IHn.
  exact/equivs_hack_f.
Qed.

Inductive fdfs_path x y : Prop :=
  FDfsPath p of path (fun x => sfrel f ^~ x) x p & y = last x p.

Lemma fdfs_dom_Nmem x y n: x \notin F -> y \in F ->
  y \notin fdfs n [::] x.
Proof.
  move=>/[dup] I + I'.
  rewrite in_fsetU negb_or => /andP[/fsfun_dflt]; case: n=> //= ? ->/= _.
  by rewrite ?inE; apply/negP=> /eqP E; rewrite E in I'; move/negbTE: I I'=>->.
Qed.

Lemma NmemF x: x \notin F ->
  fdfs n [::] x = [:: x].
Proof. by rewrite /= ?inE negb_or memNfinsupp=> /andP[/eqP->]. Qed.

Lemma fdfs_codom_Nmem x y n: x \in F -> y \notin F ->
  y \notin fdfs n [::] x.
Proof.
  move=> L; move/(_ erefl)/equivsP: (@fdfsE [::] [::] n [`L]).
  rewrite -[x]/(fsval [` L])=> -> H; apply/negP=> /mapP=> [[[/=? I _ E]]].
  by rewrite -E (negbTE H) in I.
Qed.

Lemma fdfsP x y: 
  reflect (fdfs_path x y) (y \in fdfs n [::] x).
Proof.
  case L : (x \in F); first last.
  - rewrite NmemF; last exact/negbT; rewrite ?inE.
    apply/(equivP eqP); split=> [->|[[]//=]]; first exact/(FDfsPath _ [::]).
    move=> ??; rewrite /sfrel /=; move/negbT: L.
    rewrite in_fsetU negb_or=> /andP[/fsfun_dflt]->; by rewrite ?inE.
  case L' : (y \in F); first last.
  - rewrite (negbTE (fdfs_codom_Nmem _ _ _ _ _))//; last exact/negbT.
    constructor=> [[]]; elim/last_ind=> //= [? E|]; first by rewrite E L in L'.
    move=>> ?; rewrite last_rcons rcons_path=> /andP[_ /[swap]<-] /memF.
    by rewrite L'.
  rewrite -[y]/(fsval [`L']) (@equivs_mem _ (dfs hack_f n [::] [`L])).
  apply/(equivP (dfs_pathP _ _ _ _))=> //=.
  - by rewrite cardfE card0 add0n leqnSn.
  - split=> [][] p P l.
    - move=> _; apply/(FDfsPath _ [seq val x | x <- p]).
      - rewrite (rpath equiv (grel hack_f) [`L] p) /equiv //= /sfrel /=.
        - move=>> /eqP->/eqP->; exact/equivs_mem/equivs_hack_f.
        exact/equivsP.
      elim/last_ind: p P l=> //= [_ []|????]//.
      by rewrite map_rcons ?last_rcons=> <-.
    apply/(@DfsPath _ _ _ _ _ [seq [`path_memF P (valP z)] | z <- seq_in p]).
    - rewrite -(rpath equiv _ _ _ (fun x=> (sfrel f)^~ x) p x)/equiv=> //.
      - move=>>/eqP->/eqP->; exact/equivs_mem/equivs_hack_f.
      by apply/equivsP; rewrite -map_comp -{1}(val_seq_in p) -eq_in_map.
    - elim/last_ind: p l P=> //= [? _|]; first exact/val_inj.
      move=> ? z? +*; rewrite seq_inE last_rcons -{12}cats1 pmap_cat map_cat.
      move=> /=; case: insubP=> /=.
      - move=> [??]; rewrite cats1 last_rcons /==> ? {1}<- *; exact/val_inj.
      rewrite mem_rcons inE eq_refl //.
    by rewrite disjoint_sym disjoint0.
  exact/fdfsE.
Qed.

Definition wsuffix x := fdfs n [::] x.

Definition rt_closure : rel T := 
  fun x y => x \in wsuffix y.

Lemma t_closure_n1P x y : 
  reflect (clos_refl_trans_n1 T (sfrel f) x y) (rt_closure x y).
Proof.
  apply/(equivP (fdfsP y x)); split=> [[p]|].
  - elim: p x y=> //= [>_->|]; first by constructor.
    move=> a > IHp > /andP[? /IHp /[apply] ?]; exact/(rtn1_trans _ _ _ a).
  elim=> [|z ??? [p *]]; first exact/(FDfsPath _ [::]).
  apply/(FDfsPath _ (z :: p))=> //; exact/andP.
Qed.

End FinRTClosure.

End FinClosure.

