From Coq Require Import Relations Relation_Operators.
From RelationAlgebra Require Import lattice monoid rel kat_tac.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype seq order choice.
From mathcomp Require Import finmap fingraph fintype finfun ssrnat path.
From Equations Require Import Equations.
From monae Require Import hierarchy monad_model.
From eventstruct Require Import utilities wftype monad.

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
Local Open Scope monae_scope.

Import NDMonadMorphism.Syntax.

(* A shorter name for list monad. 
 * TODO: rename to Seq? 
 * TODO: Use canonical structures to infer the 
 *   monad instance for seq automatically?  
 *)
Local Notation List := ModelNondet.list.

(* TODO: rename to `mrel` and move to `monad.v` ? *)
Definition sfrel {M : nondetMonad} {η : M ≈> List}
  {T : eqType} (f : T -> M T) : {dhrel T & T} :=
    [rel a b | b \in η T (f a)].

Section Strictify.

Context (T : eqType).
Variable  (M : nondetMonad) (η : M ≈> List).
Implicit Type (f : T -> M T).

Definition strictify f : T -> M T :=
  fun x => mfilter M (f x) (fun y => x != y).

Lemma strictify_weq f :
  @sfrel M η T (strictify f) ≡ (@sfrel M η T f \ eq_op).
Proof. 
  move=> x y; rewrite /sfrel /strictify /mfilter /=.
  by rewrite mem_mfilter andbC. 
Qed.

Lemma strictify_leq f : 
  @sfrel M η T (strictify f) ≦ @sfrel M η T f.
Proof. by rewrite strictify_weq; lattice. Qed.

End Strictify. 

Module WfClosure.

Section WfRTClosure.

Context {disp : unit} {T : wfType disp}.

Variable (M : nondetMonad) (η : M ≈> List) (f : T -> M T).

(* Hypothesis descend : forall x y, y \in f x -> y < x. *)
Hypothesis descend : @sfrel M η T f ≦ (>%O).

(* A hack to get around a bug in Equations 
 * (see https://github.com/mattam82/Coq-Equations/issues/241).
 * In short, we cannot express this function directly in Equations' syntax
 * (we can do it by adding `noind` specifier, but then we cannot use `funelim`).
 * Thus we have to "tie a recursive knot" manually. 
 *)
 Definition suffix_aux (x : T) (rec : forall y : T, y < x -> M T) := 
  let ys := f x in 
  let ps := ys >>= (fun x => 
    if x \in η T ys =P true is ReflectT pf then
      rec x (descend _ _ pf)
    else
      Fail
  ) in 
  Alt ys ps.

(* strict suffix of an element `x`, i.e. a set { y | x R y } *)
Equations suffix (x : T) : M T by wf x (<%O : rel T) := 
  suffix x := suffix_aux x suffix.

(* weak suffix of an element `x`, i.e. a set { y | x R? y } *)
Definition wsuffix (x : T) : M T :=
  Alt (Ret x) (suffix x).

(* decidable transitive closure *)
Definition t_closure : {dhrel T & T} := 
  fun x y => y \in η T (suffix x).

(* decidable reflexive-transitive closure *)
Definition rt_closure : {dhrel T & T} := 
  fun x y => y \in η T (wsuffix x).
  
(* ************************************************************************** *)
(*       THEORY                                                               *)
(* ************************************************************************** *)

Lemma t_closure_1nP x y : 
  reflect (clos_trans_1n T (@sfrel M η T f) x y) (t_closure x y).
Proof.
  rewrite /t_closure. funelim (suffix x)=> /=. 
  apply /(iffP idP); rewrite mem_alt /sfrel /=.
  { move=> /orP[|/mem_bindP[z]] //; first exact: t1n_step.
    case: eqP=> // S /descend yz /X tr. 
    move: (tr yz) => H.
    by apply: t1n_trans; first exact: S. }
  move: X=> /[swap] [[?->//|{}y ? /[dup] ? L /[swap]]].
  move=> /[apply] H; apply/orP; right; apply/mem_bindP.
  exists y=> //. case: eqP => // /descend yz. exact: H.
Qed.

Lemma t_closureP x y :
  reflect (clos_trans T (@sfrel M η T f) x y) (t_closure x y).
Proof.
  apply /(equivP (t_closure_1nP x y)).
  symmetry; exact: clos_trans_t1n_iff.
Qed.

Lemma clos_trans_gt : 
  clos_trans T (@sfrel M η T f) ≦ (>%O : rel T).
Proof. 
  move=> ??; rewrite/sfrel /=.
  elim=> [y z /descend | x y z _ ] //=.
  move=> /[swap] _ /[swap]; exact: lt_trans.
Qed.

Lemma t_closure_gt : t_closure ≦ (>%O : rel T).
Proof. by move=> x y /t_closureP /clos_trans_gt. Qed.

Lemma t_closure_antisym : antisymmetric t_closure.
Proof.
  move=> x y /andP[] /t_closure_gt ? /t_closure_gt ?. 
  by apply /eqP; rewrite eq_le !ltW.
Qed.

Lemma t_closure_trans : transitive t_closure.
Proof.
  move=> y x z /t_closureP ? /t_closureP ?.
  apply /t_closureP /t_trans; eauto. 
Qed.

Lemma rt_closureP x y :
  reflect (clos_refl_trans T (@sfrel M η T f) x y) (rt_closure x y).
Proof.
  apply /equivP; last first.
  { rewrite clos_refl_transE clos_refl_hrel_qmk. 
    apply or_iff_compat_l; symmetry.
    apply rwP; exact: t_closureP. }
  rewrite /t_closure /rt_closure /wsuffix mem_alt mem_ret eq_sym /=.
  by apply predU1P.
Qed.

Lemma rt_closureE : rt_closure ≡ t_closure^?.
Proof. 
  move=> x y /=; rewrite /rt_closure /t_closure /wsuffix. 
  rewrite alt_morph /Alt /= /monae_lib.curry /= mem_cat /dhrel_one.
  by rewrite mem_ret eq_sym.
Qed.

Lemma rt_closure_ge : rt_closure ≦ (>=%O : rel T).
Proof.
  rewrite rt_closureE.
  move=> x y /orP[/eqP<-//=|].
  move=> /t_closure_gt; exact: ltW.
Qed.

Lemma rt_closure_refl x : rt_closure x x.
Proof.
  rewrite /rt_closure alt_morph /Alt /= /monae_lib.curry /= mem_cat.
  by rewrite mem_ret eq_refl. 
Qed.

Lemma rt_closure_antisym : antisymmetric rt_closure.
Proof.
  move=> x y /andP[]. 
  move=> /rt_closure_ge /= xy /rt_closure_ge /= yx. 
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

Lemma equivs_mem v' v x: equivs v v' -> (fsval x) \in v = (x \in v').
Proof.
  elim: v v'=> [[]//|?? IHv []//= ? l /andP[+ /IHv]].
  rewrite ?inE=> /eqP->->; by rewrite val_eqE.
Qed.

Lemma equivs_hack_f x: equivs (f (fsval x)) (hack_f x).
Proof.
  by apply/equivsP; rewrite -map_comp -{1}(val_seq_in (f _)) -eq_in_map.
Qed.

Lemma path_memF {x p y}: 
  path (fun x : T => (@sfrel ModelNondet.list id_ndmorph T f) x) x p ->
  y \in p -> y \in F.
Proof.
  elim: p x=> //= ?? IHp ? /andP[]. rewrite /sfrel /= => /memF ? /IHp ?.
  by rewrite inE=> /orP[/eqP->|].
Qed.

Lemma fdfsE {v v' n} {x : F} :
  equivs v v' ->
  equivs (fdfs n v (fsval x)) (dfs hack_f n v' x).
Proof.
  elim: n v v' x=> n IHn v v' //=; first by (do ?case: ifP).
  move=> x E; rewrite (equivs_mem v' v) // /hack_f; case: ifP=> // ?.
  apply (@rfoldl (seq T) T (seq F) F equivs equiv).
  - by rewrite /= /equiv eq_refl. 
  - move=> ????? /eqP ->; exact/IHn.
  exact/equivs_hack_f.
Qed.

Definition fdfs_path x y : Prop :=
  exists2 p, path (fun a => @sfrel _ id_ndmorph T f a) x p & y = last x p.

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
    apply/(equivP eqP); split=> [->|[[]//=]]; first by exists [::].
    move=> ??; rewrite /sfrel /=; move/negbT: L.
    rewrite in_fsetU negb_or=> /andP[/fsfun_dflt]->; by rewrite ?inE.
  case L' : (y \in F); first last.
  - rewrite (negbTE (fdfs_codom_Nmem _ _ _ _ _))//; last exact/negbT.
    constructor=> [[]]; elim/last_ind=> //= [? E|]; first by rewrite E L in L'.
    move=>> ?; rewrite last_rcons rcons_path=> /andP[_ /[swap]<-] /memF.
    by rewrite L'.
  rewrite -[y]/(fsval [`L']) (equivs_mem (dfs hack_f n [::] [`L])); first last.
  - exact/fdfsE.
  apply /(equivP (dfs_pathP _ _ _ _))=> //=.
  - by rewrite cardfE card0 add0n leqnSn.
  - split=> [][] p P l.
    - move=> _; exists [seq val x | x <- p].
      - rewrite (@rpath T F equiv (grel hack_f) [`L] p) /equiv //= /sfrel /=.
        - move=>> /eqP->/eqP->; exact/equivs_mem/equivs_hack_f.
        exact/equivsP.
      elim/last_ind: p P l=> //= [_ []|????]//.
      by rewrite map_rcons ?last_rcons=> <-.
    apply/(@DfsPath _ _ _ _ _ [seq [`path_memF P (valP z)] | z <- seq_in p]).
    - rewrite -(@rpath T F equiv _ _ _ (fun x=> (@sfrel _ id_ndmorph T f) x) p x)/equiv=> //.
      - move=>>/eqP->/eqP->; exact/equivs_mem/equivs_hack_f.
      by apply/equivsP; rewrite -map_comp -{1}(val_seq_in p) -eq_in_map.
    - elim/last_ind: p l P=> //= [? _|]; first exact/val_inj.
      move=> ? z? +*; rewrite seq_inE last_rcons -{12}cats1 pmap_cat map_cat.
      move=> /=; case: insubP=> /=.
      - move=> [??]; rewrite cats1 last_rcons /==> ? {1}<- *; exact/val_inj.
      rewrite mem_rcons inE eq_refl //.
    by rewrite disjoint_sym disjoint0.
Qed.

Definition wsuffix x := fdfs n [::] x.

Definition suffix x := flatten [seq f y | y <- wsuffix x].

Definition rt_closure : rel T := 
  fun x y => y \in wsuffix x.

Definition t_closure : rel T := 
  fun x y => y \in suffix x.

Lemma rt_closure_1nP x y : 
  reflect (clos_refl_trans_1n T (@sfrel _ id_ndmorph T f) x y) (rt_closure x y).
Proof.
  apply/(equivP (fdfsP x y)); split=> [[p]|].
  - elim: p x y=> //= [>_->|]; first by constructor.
    move=> a > IHp > /andP[? /IHp /[apply] ?]; exact/(rt1n_trans _ _ _ a).
  elim=> [|{}x {}y {}z ?? [p *]]; first by exists [::]. 
  exists (y :: p)=> //. exact/andP.
Qed.

Arguments clos_rtn1_rt {_ _ _ _}.
Arguments clos_rt_rtn1 {_ _ _ _}.
Arguments clos_trans_tn1 {_ _ _ _}.
Arguments clos_trans_t1n {_ _ _ _}.
Arguments clos_tn1_trans {_ _ _ _}.
Arguments clos_t1n_trans {_ _ _ _}.
Arguments t1n_trans _ {_ _ _ _}.

Lemma t_closure_n1P x y: 
  reflect (clos_trans_1n T (@sfrel _ id_ndmorph T f) x y) (t_closure x y).
Proof.
  apply: (iffP flatten_mapP)=> [[z]|]. 
  - move=> /rt_closure_1nP H ?. apply/clos_trans_t1n/clos_rt_t.
    - apply/clos_rt1n_rt; exact: H.
    - by apply/t_step.
  case=> [z|z {}y]; first exists x=> //.
  - apply/rt_closure_1nP/rt1n_refl.
  move=> H /clos_t1n_trans/clos_trans_tn1 [{}y|].
  - move=> ?; exists z=> //.
    by apply/rt_closure_1nP/clos_rt1n_step.
  move=> {}y {}z' ??. exists y=> //.
  apply/rt_closure_1nP/rt1n_trans; first exact: H. 
  by apply/clos_rt_rt1n/clos_t_clos_rt/clos_tn1_trans.
Qed.

End FinRTClosure.

End FinClosure.
