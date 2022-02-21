From Coq Require Import Relations Relation_Operators.
From RelationAlgebra Require Import lattice monoid rel kat_tac.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat zify. 
From mathcomp Require Import eqtype choice seq order path.
From mathcomp Require Import fintype finfun fingraph finmap.
From mathcomp.tarjan Require Import extra acyclic kosaraju acyclic_tsorted. 
From Equations Require Import Equations.
From eventstruct Require Import utils relalg wftype.

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
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations Transparent.

Import Order.LTheory.
Local Open Scope order_scope.
Local Open Scope ra_terms.

Section Rel.
Context {T : Type}.
Implicit Types (r : rel T). 

Lemma refl_cap r1 r2 :
  reflexive r1 -> reflexive r2 -> reflexive (r1 ⊓ r2).
Proof. by move=> refl1 refl2 x /=; apply/andP. Qed.

Lemma antisym_cap r1 r2 :
  antisymmetric r1 -> antisymmetric (r1 ⊓ r2).
Proof. 
  move=> asym x y /=. 
  rewrite -andbA=> /and4P[????].
  by apply/asym/andP.
Qed.

Lemma trans_cap r1 r2 :
  transitive r1 -> transitive r2 -> transitive (r1 ⊓ r2).
Proof. 
  move=> trans1 trans2 z x y /=. 
  move=> /andP[??] /andP[??]; apply/andP. 
  by firstorder.
Qed.

Lemma eq_irrefl r1 r2 : 
  r1 =2 r2 -> irreflexive r1 <-> irreflexive r2.
Proof. 
  move=> eqr; split=> irr x. 
  - rewrite -eqr; exact/irr.
  rewrite eqr; exact/irr.
Qed.

Lemma eq_antisym r1 r2 : 
  r1 =2 r2 -> antisymmetric r1 <-> antisymmetric r2.
Proof. 
  move=> eqr; split=> anti x y.
  - rewrite -eqr -eqr; exact/anti.
  rewrite !eqr; exact/anti.
Qed.

Lemma eq_trans r1 r2 : 
  r1 =2 r2 -> transitive r1 <-> transitive r2.
Proof. 
  move=> eqr; split=> trans z x y.
  - rewrite -?eqr; exact/trans.
  rewrite ?eqr; exact/trans.
Qed.

End Rel.

Section ClosRefl.
Context {T : eqType}.
Implicit Types (r : {dhrel T & T}). 

Lemma dhrel_qmkE r :
  r^? =2 [rel x y | (x == y) || (r x y)].
Proof. done. Qed.

Lemma qmk_refl r :
  reflexive r^?.
Proof. by move=> x; rewrite dhrel_qmkE /= eqxx. Qed.

Lemma qmk_antisym r :
  antisymmetric r -> antisymmetric r^?.
Proof. 
  move=> asym x y; rewrite !dhrel_qmkE /=.
  move=> /andP[] /orP[/eqP->|?] // /orP[/eqP->|?] //.
  by apply/asym/andP.  
Qed.
  
Lemma qmk_trans r :
  transitive r -> transitive r^?.
Proof.
  move=> trans z x y; rewrite !dhrel_qmkE /=.
  move=> /orP[/eqP<-|rxz] // /orP[/eqP<-|rzy] //.
  apply/orP; right; apply/trans; [exact/rxz|exact/rzy]. 
Qed.

End ClosRefl.

Section SubRelLift.
Context {T : eqType} {U : Type} {P : pred T} {S : subType P}.

Lemma sub_rel_lift_qmk (r : {dhrel S & S}) :
  (sub_rel_lift r : {dhrel T & T})^? =2 (sub_rel_lift r^? : {dhrel T & T})^?. 
Proof. 
  move=> x y; rewrite !dhrel_qmkE /=.
  apply/idP/idP=> [/orP[|]|].
  - by move=> /eqP->; rewrite eqxx. 
  - move=> /sub_rel_liftP[] x' [] y' [] ? <- <-.
    apply/orP; right; apply/sub_rel_liftP. 
    exists x', y'; split=> //=.
    by apply/orP; right. 
  move=> /orP[/eqP->|]; rewrite ?eqxx //.
  move=> /sub_rel_liftP[] x' [] y' [] /= + <- <-.
  move=> /orP[/eqP->|]; rewrite ?eqxx //.
  move=> ?; apply/orP; right; apply/sub_rel_liftP.
  by exists x', y'.
Qed.

End SubRelLift.

Section FinGraph. 
Context {T : finType}.
Implicit Types (g : rel T). 
Implicit Types (gf : T -> seq T). 

Definition irreflexiveb g :=
  [forall x, ~~ g x x].

Definition antisymmetricb g :=
  [forall x, forall y, g x y && g y x ==> (x == y)].

Definition totalb g :=
  [forall x, forall y, g x y || g y x].

Lemma irreflexiveP g : 
  reflect (irreflexive g) (irreflexiveb g).
Proof. apply/forallPP=> ?; exact/negPf. Qed.

Lemma antisymmetricP g : 
  reflect (antisymmetric g) (antisymmetricb g).
Proof. do 2 apply/forallPP=> ?; exact/(implyPP idP)/eqP. Qed.

Lemma totalP g : 
  reflect (total g) (totalb g).
Proof. exact/forall2P. Qed.

Lemma connect_refl g : 
  reflexive (connect g).
Proof. done. Qed. 

Lemma preacyclicE g :
  preacyclic g = antisymmetricb (connect g).
Proof. done. Qed.

Lemma acyclicE g :
  acyclic g = irreflexiveb g && antisymmetricb (connect g).
Proof. done. Qed.

Lemma acyc_irrefl g :
  acyclic g -> irreflexive g.
Proof. 
  move=> /acyclicP[irr _] x. 
  move: (irr x)=> /negP ?; exact/negP. 
Qed.

Lemma acyc_antisym g : 
  acyclic g -> antisymmetric (connect g).
Proof. 
  move=> /acyclic_symconnect_eq symconE x y.
  move: (symconE x y); rewrite /symconnect.
  by move=> -> /eqP.
Qed.

Lemma mem_tseq gf : 
  tseq gf =i enum T.
Proof. 
  move: (tseq_correct gf)=> [_ in_tseq]. 
  apply/subset_eqP/andP; split; apply/subsetP; last first.
  - move=> x ?; exact/in_tseq. 
  by move=> ?; rewrite mem_enum.
Qed.

Lemma size_tseq gf : 
  size (tseq gf) = #|T|.
Proof. 
  rewrite cardT; apply/eqP. 
  rewrite -uniq_size_uniq.
  - exact/tseq_uniq.
  - exact/enum_uniq.
  move=> ?; exact/esym/mem_tseq.
Qed.

End FinGraph. 

Section SubFinGraph. 
Context {T : choiceType} {fT : {fset T}}.
Implicit Types (g : rel fT). 

Lemma sub_rel_lift_connect g : 
  (sub_rel_lift g : hrel T T)^* ≡ (sub_rel_lift (connect g) : hrel T T)^?.
Proof. 
  move=> x y; split.
  - move=> /clos_rt_str; elim.
    + move=> {}x {}y /=.
      rewrite /sub_rel_lift /=.
      case: insubP=> //.
      case: insubP=> //.
      move=> ???????; right; exact/connect1.
    + by move=> {}x /=; left.
    move=> ???? [->|xy] ? [<-|yz] /=; [left|right|right|] => //. 
    right; apply/(sub_rel_lift_trans _ xy yz).
    exact/connect_trans.
  move=> xy; apply/clos_rt_str.
  move: xy; rewrite /sub_rel_lift /=.
  move=> [->|].
  - exact/rt_refl.
  case: insubP=> //.
  case: insubP=> //.
  move=> /= y' yIn <- x' xIn <-.
  move=> /connect_strP/clos_rt_str; elim. 
  - move=> /= x'' y'' xy; apply/rt_step. 
    rewrite !insubT //. 
    move=> ??; rewrite !sub_val //.
  - move=> ?; exact/rt_refl.
  move=> ???? xy ? yz; apply/rt_trans; [exact/xy | exact/yz].
Qed.

End SubFinGraph.

Section RelMono. 
Context {T U : Type}.
Variables (f : T -> U) (g1 : rel T) (g2 : rel U).
Hypothesis (fbij : bijective f).
Hypothesis (fmon : {mono f : x y / g1 x y >-> g2 x y}).

Lemma irreflexive_mono : 
  (irreflexive g1) <-> (irreflexive [rel x y | g2 (f x) (f y)]).
Proof. 
  split=> irr x /=. 
  - by rewrite fmon. 
  rewrite -fmon; exact/irr.
Qed.

Lemma antisymmetric_mono : 
  (antisymmetric g1) <-> (antisymmetric [rel x y | g2 (f x) (f y)]).
Proof. 
  split=> asym x y /=.
  - rewrite !fmon; exact/asym.
  rewrite -fmon -fmon; exact/asym.
Qed.

End RelMono.

Section FinGraphMono. 
Context {T U : finType}.
Implicit Types (f : T -> U) (gT : rel T) (gU : rel U).

Lemma connect_mono f gT gU : bijective f -> 
  {mono f : x y / gT x y >-> gU x y} ->
  {mono f : x y / connect gT x y >-> connect gU x y}.
Proof. 
  move=> fbij fmon x y; apply/idP/idP; last first.
  all: move=> /connect_strP/clos_rt_str/=> crt. 
  all: apply/connect_strP/clos_rt_str. 
  - elim: crt=> // [|??? _ + _]; last exact/rt_trans.
    move=> {}x {}y; rewrite -fmon; exact/rt_step.
  move: fbij=> [g] K K'.
  rewrite -[x]K -[y]K.
  elim: crt=> // [|??? _ + _]; last exact/rt_trans.
  move=> {}x {}y; rewrite -[x]K' -[y]K' fmon=> ?. 
  by apply/rt_step; rewrite !K.
Qed.

End FinGraphMono.

(* TODO: rename? consult theory? unify with strictify? *)
Section IKer. 
Context {T : eqType}.
Implicit Type (r : rel T).

Definition iker r : rel T := 
  fun x y => (y != x) && r x y.

Lemma iker_qmk r : 
  reflexive r -> (iker r : {dhrel T & T})^? =2 r.
Proof. 
  move=> refl x y ; rewrite dhrel_qmkE /= /iker.
  apply/idP/idP=> [/orP[|]|].
  - by move=> /eqP->; rewrite refl.
  - by move=> /andP[].
  move=> ->; rewrite andbT. 
  case: (x == y)/idP=> //. 
  by rewrite eq_sym=> /negP ->.
Qed.

Lemma iker_irrefl r : 
  irreflexive (iker r).
Proof. by move=> x; rewrite /iker eqxx. Qed.

Lemma iker_antisym r : 
  antisymmetric r -> antisymmetric (iker r).
Proof. 
  move=> asym x y /andP[] /andP[??] /andP[??].
  exact/asym/andP.
Qed.

Lemma iker_trans r : 
  antisymmetric r -> transitive r -> transitive (iker r).
Proof. 
  move=> asym trans z x y /andP[/eqP nzx rxz] /andP[/eqP nzy rzy].
  apply/andP; split; last first.
  - apply/trans; [exact/rxz|exact/rzy].
  apply/negP=> /eqP eyx. 
  by apply/nzx/asym/andP; split=> //; rewrite -eyx.
Qed.

End IKer.

Section Covering.
Context {T : finType}.
Implicit Types (r : rel T).

Definition gfun r := 
  fun x => filter (r x) (enum T).

Lemma gfun_inE r x y :
  y \in (gfun r x) = r x y.
Proof. by rewrite /gfun mem_filter mem_enum inE andbT. Qed.

Definition cov r : rel T := 
  [rel x y | [&& (x != y) , (r x y) & ~~ [exists z, r x z && r z y]]].

Definition cov_tseq r x y := 
  let t := tseq (rgraph r) in
  let p := [pred z | r x z && r z y] in
  let ix := index x t in 
  let iy := index y t in 
  ~~ has p (slice ix iy t). 
  (* [rel x y | index y t - (index x t).+1 == find (r x) (drop (index x t).+1 t)]. *)

Lemma cov_subrel r : 
  subrel (cov r) r.
Proof. by move=> ?? /and3P[]. Qed.

(* TODO: reformulate in terms of relation algebra? *)
Lemma covP r x y : 
  reflect [/\ x <> y , r x y & ~ exists z, r x z && r z y] (cov r x y).
Proof. 
  rewrite /cov; apply/(equivP and3P). 
  split; case=> ???; split=> //; try exact/eqP; 
    exact/(negPP existsP).
Qed.

Lemma cov_irrefl r : 
  irreflexive (cov r).
Proof. by move=> x; apply/negP=> /andP[]; rewrite eq_refl. Qed.

Lemma cov_sliceP r x y : 
  let t := tseq (rgraph r) in
  let p := [pred z | r x z && r z y] in
  let ix := index x t in 
  let iy := index y t in 
  (*   *)
  acyclic r -> reflect (exists z, r x z && r z y) 
                       (has p (slice ix iy t)).
Proof. 
  move=> /= acyc; apply/(equivP idP); split. 
  - by move=> /hasP[z] zIn /= ?; exists z.
  move=> [z] /andP[rxz rzy].
  apply/hasP; exists z=> //=; last exact/andP.
  rewrite in_slice_index; last first.
  - exact/tseq_uniq. 
  - apply/andP; split; last exact/index_size.
    apply/(tseq_rel_connect_before acyc).
    apply/connect_trans; apply/connect1; [exact/rxz | exact/rzy].
  apply/andP; split.
  - move: rxz=> /[dup] rxz. 
    move=> /connect1/(tseq_rel_connect_before acyc).
    by rewrite /before.
  move: rzy=> /[dup] rzy. 
  move=> /connect1/(tseq_rel_connect_before acyc).
  rewrite /before leq_eqVlt=> /orP[/eqP|] //.
  move=> /index_inj eq_zy; exfalso.
  move: (acyc_irrefl acyc)=> irr; move: (irr z). 
  by rewrite {2}eq_zy ?rzy ?mem_tseq ?mem_enum.
Qed.

Lemma cov_connect r x y :
  acyclic r -> r x y -> connect (cov r) x y.
Proof.  
  move=> acyc rxy.
  pose t  := tseq (rgraph r).
  pose p  := [pred z | r x z && r z y].
  pose ix := index x t.
  pose iy := index y t.
  pose s  := slice ix iy t.
  have [n leN] := ubnP (size s).
  subst t p ix iy s.
  move: x y rxy leN; elim: n=> // n IH x y rxy.
  pose t  := tseq (rgraph r).
  pose p  := [pred z | r x z && r z y].
  pose ix := index x t.
  pose iy := index y t.
  pose s  := slice ix iy t.
  rewrite -/t -/s -/ix -/iy => sz.
  case: (x == y)/idP => [/eqP->|/negP/eqP neq_xy] //.
  case: (has p s)/idP; last first.
  - move=> hasN; apply/connect1.
    apply/covP; split=> //.
    by move=> /(cov_sliceP _ _ acyc).
  move=> /hasP[z] zIn /andP[rxz rzy].  
  pose iz := index z t.
  have iy_sz: (iy <= size t)%N. 
  - by apply/ltnW; rewrite index_mem mem_tseq mem_enum. 
  have iz_sz: (iz <= size t)%N. 
  - by apply/ltnW; rewrite index_mem mem_tseq mem_enum.
  have : (ix <= iz < iy)%N.
  - rewrite -in_slice_index //; last exact/tseq_uniq. 
    apply/andP; split=> //.
    apply/(tseq_rel_connect_before acyc).
    apply/connect_trans; apply/connect1; [exact/rxz | exact/rzy].
  move=> /andP[]; rewrite leq_eqVlt=> /orP[/eqP|] // => [+ _|ixz izy].
  - move: rxz=> /[swap] /index_inj ->; rewrite ?mem_tseq ?mem_enum //.
    by rewrite (acyc_irrefl acyc). 
  apply/(@connect_trans _ _ z); apply/IH=> //.
  all: rewrite -/ix -/iy -/iz -/t.
  all: move: sz; rewrite /s !size_slice //; lia. 
Qed.

Lemma connect_covE r x y : 
  acyclic r -> connect (cov r) x y = connect r x y.
Proof. 
  move=> acyc; apply/idP/idP.
  - by apply/connect_sub=> {}x {}y /covP[? /connect1].
  apply/connect_sub=> {}x {}y; exact/cov_connect.  
Qed.

Lemma iker_connect r : 
  connect (iker r) =2 connect r.
Proof.
  move=> x y; apply/(sameP (connect_strP _ _ _))/(equivP (connect_strP _ _ _)).
  rewrite kleene.str_weq1; first reflexivity.
  rewrite -qmk_sub_one; first apply/qmk_weq=> ?? /=.
  - rewrite /iker eq_sym.
    split=> [[]|/andP[/eqP ?]] * //. 
    by apply/andP; split=> //; apply/eqP. 
  move=> a b /=; split=> // ?; case: (a =P b); by (left+right).
Qed.

End Covering.

(* TODO: rename to `mrel` and move to `monad.v` ? *)
Definition sfrel {T : eqType} (f : T -> seq T) : {dhrel T & T} :=
    [rel a b | b \in f a].

Section Strictify.
Context {T : eqType}.
Implicit Type (f : T -> seq T).

Definition strictify f : T -> seq T :=
  fun x => filter^~ (f x) (fun y => x != y).

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

Set Strict Implicit.

Module WfClosure.

Section WfRTClosure.

Context {disp : unit} {T : wfType disp}.

Variable (f : T -> seq T).

(* Hypothesis descend : forall x y, y \in f x -> y < x. *)
Hypothesis descend : sfrel f ≦ (>%O).

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
  )) in 
  ys ++ ps.

(* strict suffix of an element `x`, i.e. a set { y | x R y } *)
Equations suffix (x : T) : seq T by wf x (<%O : rel T) := 
  suffix x := suffix_aux x suffix.

(* weak suffix of an element `x`, i.e. a set { y | x R? y } *)
Definition wsuffix (x : T) : seq T :=
  x :: suffix x.

(* decidable transitive closure *)
Definition t_closure : {dhrel T & T} := 
  fun x y => y \in suffix x.

(* decidable reflexive-transitive closure *)
Definition rt_closure : {dhrel T & T} := 
  fun x y => y \in wsuffix x.
  
(* ************************************************************************** *)
(*       THEORY                                                               *)
(* ************************************************************************** *)

Lemma t_closure_1nP x y : 
  reflect (clos_trans_1n (sfrel f) x y) (t_closure x y).
Proof.
  rewrite /t_closure; funelim (suffix x)=> /=. 
  apply /(iffP idP); rewrite mem_cat /sfrel /=.
  - move=> /orP[|/flatten_mapP[z]] //; first exact: t1n_step.
    move=> S /X H. apply: t1n_trans (valP z) _.
    by apply: H=> //=; apply: descend (valP z).
  move: X=> /[swap] [[?->//|{}y ? /[dup] ? L /[swap]]].
  move=> /[apply] H; apply/orP; right; apply/flatten_mapP.
  eexists; first by apply: seq_in_mem L.
  by apply /H=> //=; apply: descend.
Qed.

Lemma t_closureP x y :
  reflect (clos_trans (sfrel f) x y) (t_closure x y).
Proof.
  apply /(equivP (t_closure_1nP x y)).
  symmetry; exact: clos_trans_t1n_iff.
Qed.

Lemma clos_trans_gt : 
  clos_trans (sfrel f) ≦ (>%O : rel T).
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
  reflect (clos_refl_trans (sfrel f) x y) (rt_closure x y).
Proof.
  apply /equivP; last first.
  { rewrite clos_rt_crE clos_r_qmk. 
    apply or_iff_compat_l; symmetry.
    apply rwP; exact: t_closureP. }
  rewrite /t_closure /rt_closure /wsuffix in_cons eq_sym /=.
  by apply predU1P.
Qed.

Lemma rt_closureE : rt_closure ≡ t_closure^?.
Proof. 
  move=> x y /=; rewrite /rt_closure /t_closure /wsuffix. 
  by rewrite /dhrel_one in_cons eq_sym. 
Qed.

Lemma rt_closure_ge : rt_closure ≦ (>=%O : rel T).
Proof.
  rewrite rt_closureE.
  move=> x y /orP[/eqP<-//=|].
  move=> /t_closure_gt; exact: ltW.
Qed.

Lemma rt_closure_refl x : rt_closure x x.
Proof. rewrite /rt_closure /= /wsuffix; exact/mem_head. Qed. 

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
  path (fun x : T => (sfrel f) x) x p ->
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
  exists2 p, path (fun a => sfrel f a) x p & y = last x p.

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
    - rewrite -(@rpath T F equiv _ _ _ (fun x=> sfrel f x) p x)/equiv=> //.
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
  reflect (clos_refl_trans_1n T (sfrel f) x y) (rt_closure x y).
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
  reflect (clos_trans_1n (sfrel f) x y) (t_closure x y).
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
  by apply/clos_rt_rt1n/clos_t_rt/clos_tn1_trans.
Qed.

End FinRTClosure.

End FinClosure.
