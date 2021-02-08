From Coq Require Import Relations Relation_Operators.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype seq order.
From RelationAlgebra Require Import lattice rel.
From Equations Require Import Equations.
From event_struct Require Import utilities wftype.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Set Equations Transparent.

Import Order.LTheory.
Local Open Scope order_scope.
(* Local Open Scope ra_terms. *)

(* a hack to bypass a shadowing problem caused by relation-algebra import *)
Local Notation antisymmetric  := Coq.ssr.ssrbool.antisymmetric.
Local Notation transitive := Coq.ssr.ssrbool.transitive.

Declare Scope rel_scope.
Delimit Scope rel_scope with REL.

Local Open Scope rel_scope.

(* For uniformity, for the converse operation 
 * we use the same notation as the relation-algebra  
 * (but at different interpretation scope) 
 *)
Reserved Notation "r °" (at level 5, left associativity, format "r °").

Section SeqFunRel.

Context {T : eqType}.

Definition sfrel (f : T -> seq T) : rel T := [rel a b | b \in f a].

Definition strictify (f : T -> seq T) : T -> seq T :=
  fun n => filter^~ (f n) (fun x => x != n).

Lemma strictify_weq (f : T -> seq T) :
  sfrel (strictify f) ≡ (sfrel f \ eq_op).
Proof. 
  move=> x y. rewrite /sfrel /strictify //=.
  by rewrite /=mem_filter andbC eq_sym.
Qed.

Lemma strictify_leq (f : T -> seq T) : 
  sfrel (strictify f) ≦ sfrel f.
Proof. by rewrite strictify_weq; lattice. Qed.

End SeqFunRel.

Section ConverseDef.

Context {T : Type}.

(* Converse (a.k.a inverse, transposition) of the decidable relation.
 * We define it from scratch here so that later 
 * we can use it as unary operation on relations  
 * (as opposed to simply use `^~` notation from mathcomp), 
 * and also to build a theory around it. 
 * We also cannot use the relation-algebra here, 
 * because there the `cnv` operation is coupled into 
 * the same structure as `dot` (composition),  
 * and the relational composition cannot be defined 
 * for decidable relations in general 
 * (although it could be defined for some particular cases, 
 *  like finite decidable relations).
 *)
Definition rel_cnv (r : rel T) : rel T := 
  fun x y => r y x.

End ConverseDef. 

Notation "r °" := (rel_cnv r) : rel_scope.

Section ConverseTheory.

Context {T : Type}.
Implicit Type (R : relation T) (r : rel T).

Lemma rel_cnvE r y : 
  rel_cnv r y = r^~ y.
Proof. by rewrite /cnv. Qed.

Lemma rel_cnvP R r : 
  (forall x y, reflect (R x y) (r x y)) -> 
  forall x y, reflect ((R : hrel _ _)°%ra x y) (r° x y).
Proof.
  move=> H x y; move: (H y x)=> /rwP [f g] /=. 
  by apply: Bool.iff_reflect. 
Qed.

End ConverseTheory.

Section DescendRTClos.

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
  )) 
  in ys ++ ps.

(* strict suffix of an element `x`, i.e. a set { y | x < y } *)
Equations suffix (x : T) : seq T by wf x (<%O : rel T) := 
  suffix x := suffix_aux x suffix.

(* weak suffix of an element `x`, i.e. a set { y | x <= y } *)
Definition wsuffix (x : T) : seq T :=
  x :: suffix x.

(* decidable transitive closure *)
Definition t_closure : rel T := 
  fun x y => y \in suffix x.

(* decidable reflexive-transitive closure *)
Definition rt_closure : rel T := 
  fun x y => y \in wsuffix x. 

(* Transitive closure reflection lemma *)
Lemma t_closure_1nP x y : 
  reflect (clos_trans_1n T (sfrel f) x y) (t_closure x y).
Proof.
  rewrite /t_closure. funelim (suffix x)=> /=. 
  apply /(iffP idP); rewrite mem_cat /sfrel /=.
  { move=> /orP[|/flatten_mapP[z]] //=; first exact: t1n_step.
    move=> zin' yin. have zin: (val z \in f x) by apply /seq_in_mem /zin'.
    apply: t1n_trans; first exact zin.
    apply: X; last exact: yin. by apply descend. }
  move=> H; case: H; clear y. 
  { by move=> y ?; apply /orP; left. }
  move=> y z yin /X Hz; apply /orP; right; apply /flatten_mapP. 
  case: (seq_in_mem_exist _ _ yin)=> y' yval' yin'.
  eexists; first by exact yin'.
  by rewrite -yval'; apply /Hz /descend.
Qed.
  
Lemma t_closureP x y :
  reflect (clos_trans T (sfrel f) x y) (t_closure x y).
Proof.
  apply /(iffP idP) => [/t_closure_1nP| cab]; first exact: clos_t1n_trans.
  apply /t_closure_1nP; exact: clos_trans_t1n.
Qed.

Lemma t_closure_cnvP x y :
  reflect (clos_trans T (sfrel f)° x y) (t_closure° x y).
Proof.
  apply /equivP; first by apply /rel_cnvP /t_closureP.
  apply: iff_trans; first by apply clos_trans_hrel_itr.
  apply: iff_trans; last by symmetry; apply clos_trans_hrel_itr.
  (* a bunch of hacks... *)
  set (r := ((fun x y : T => (sfrel f x y)) : hrel T T)).
  have ->: (r^+ y x = r^+°%ra x y); first done.
  by rewrite kleene.cnvitr. 
Qed.

Lemma clos_trans_gt : 
  clos_trans T (sfrel f) ≦ (>%O : rel T).
Proof. 
  move=> ??. rewrite/sfrel //=. 
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
  move=> y x z /t_closureP xy /t_closureP yz.
  apply /t_closureP /t_trans; first exact: xy; exact: yz.
Qed.

Lemma rt_closureP x y :
  reflect (clos_refl_trans T (sfrel f) x y) (rt_closure x y).
Proof.
  apply /equivP; last first.
  { rewrite clos_refl_transE clos_reflE. 
    apply or_iff_compat_l; symmetry.
    apply rwP; exact: t_closureP. }
  rewrite /t_closure /rt_closure /wsuffix in_cons eq_sym.
  by apply predU1P.
Qed.

Lemma rt_closure_cnvP x y :
  reflect (clos_refl_trans T (sfrel f)° x y) (rt_closure° x y).
Proof.
  apply /equivP; first by apply /rel_cnvP /rt_closureP.
  apply: iff_trans; first by apply clos_refl_trans_hrel_str.
  apply: iff_trans; last by symmetry; apply clos_refl_trans_hrel_str.
  (* a bunch of hacks... *)
  set (r := ((fun x y : T => (sfrel f x y)) : hrel T T)).
  have ->: (r^* y x = r^*°%ra x y); first done.
  by rewrite kleene.cnvstr. 
Qed.

Lemma rt_closureE : rt_closure ≡ eq_op ⊔ t_closure.
Proof. 
  move=> x y /=; rewrite /rt_closure /t_closure. 
  by rewrite /wsuffix in_cons eq_sym.
Qed.

Lemma rt_closure_ge : rt_closure ≦ (>=%O : rel T).
Proof.
  rewrite rt_closureE.
  move=> x y /orP[/eqP[<-]|] //=.
  move=> /t_closure_gt; exact: ltW.
Qed.

Lemma rt_closure_refl x : rt_closure x x.
Proof. exact: mem_head. Qed.

Lemma rt_closure_antisym : antisymmetric rt_closure.
Proof.
  move=> x y /andP[]. 
  move=> /rt_closure_ge /= xy /rt_closure_ge /= yx. 
  by apply /eqP; rewrite eq_le xy yx.
Qed.

Lemma rt_closure_trans : transitive rt_closure.
Proof.
  move=> y x z /rt_closureP xy /rt_closureP ?.
  by apply/rt_closureP /rt_trans; first exact: xy. 
Qed.

End DescendRTClos.
