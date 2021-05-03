From mathcomp Require Import ssreflect ssrbool ssrfun eqtype seq.
From monae Require Import hierarchy monad_lib monad_model.

Local Open Scope monae_scope.

Module MonadMorphism.

Record mixin_of (M N : monad) (η : M ~> N) := Mixin {
  _ : forall a, η a \o Ret = Ret;
  _ : forall a (m : M (M a)),
        η a (Join m) = Join (η (N a) ((M # (η a)) m))
}.

Structure type (M N : monad) := Pack
  { cpmm : M ~> N ; class : mixin_of M _ cpmm }.

Module Import Exports.
Notation monmorph := type.
Coercion cpmm : type >-> Natural.type.
Notation MonadMorphism p := (Pack (Mixin p)).
End Exports.

(* We do not export arrow notation by default, because we have 
 * a monad morphism class for each subclass of monads. 
 * So instead we use the same notation for all monad morphisms. 
 * The user can import locally the module with the notation 
 * for the required subclass of monads.  
 *)
Module Import Syntax.
Notation "f ≈> g" := (monmorph f g) (at level 51) : monae_scope.
End Syntax. 

Module Import Theory.
Section Theory.

Lemma ret_morph (M N : monad) (η : M ≈> N) :
  forall a, η a \o Ret = Ret.
Proof. case: η => cpmm; by case. Qed.

Lemma join_morph (M N : monad) (η: M ≈> N) :
  forall a (m : M (M a)),
    η a (Join m) = Join (η (N a) ((M # (η a)) m)).
Proof. case: η => cpmm; by case. Qed.

Lemma bind_morph (T : Type) (M N : monad) (η : M ≈> N) (m : M T) (k : T -> M T) :
  η T (m >>= k) = (η T m) >>= (fun x => η T (k x)).
Proof.
  rewrite /Bind join_morph.
  rewrite <- monad_lib.fmap_oE.
  fold (comp (η (N T)) (M # (η T \o k)) m).
  by rewrite -natural. 
Qed.

End Theory.
End Theory.

End MonadMorphism.

Export MonadMorphism.Exports.
Export MonadMorphism.Theory.

Module NDMonadMorphism.

Record mixin_of (M N : nondetMonad) (η : monmorph M N) := Mixin {
  _ : forall a, η a Fail = Fail;
  _ : forall a m n, η a (Alt m n) = Alt (η a m) (η a n)
}.

Structure type (M N : nondetMonad) := Pack
  { cpmm : monmorph M N ; class : mixin_of M _ cpmm }.

Module Import Exports.
Notation ndmonmorph := type.
Coercion cpmm : type >-> MonadMorphism.type.
Notation NDMonadMorphism p := (Pack (Mixin p)).
End Exports.

Module Import Syntax.
Notation "f ≈> g" := (ndmonmorph f g) (at level 51) : monae_scope.
End Syntax.

Module Import Theory.
Section Theory.

Lemma fail_morph (M N : nondetMonad) (η: M ≈> N) :
  forall a, η a Fail = Fail.
Proof. case: η => cpmm; by case. Qed.

Lemma alt_morph (M N : nondetMonad) (η: M ≈> N) :
  forall a m n, η a (Alt m n) = Alt (η a m) (η a n).
Proof. case: η => cpmm; by case. Qed.

End Theory.
End Theory.

End NDMonadMorphism.

Export NDMonadMorphism.Exports.
Export NDMonadMorphism.Theory.

Section ListMonadMorphismTheory.

Import NDMonadMorphism.Syntax.
Import ModelNondet ModelMonad ListMonad.

Context {T : eqType}.
Variable (M : nondetMonad) (η : M ≈> ModelNondet.list).

Lemma ret_morph_list (x : T) :
  η T (Ret x) = [:: x].
Proof. 
  have ->: η T (Ret x) = (η T \o Ret) x by done.
  by rewrite ret_morph. 
Qed.

Lemma fail_morph_list :
  η T Fail = [::].
Proof. by rewrite fail_morph. Qed.

Lemma alt_morph_list (m n : M T) : 
  η T (Alt m n) = (η T m) ++ (η T n). 
Proof. by rewrite alt_morph. Qed.

Lemma mem_ret (x y : T) :
  x \in η T (Ret y) = (x == y).
Proof.
  have ->: η T (Ret y) = (η T \o Ret) y by done.
  by rewrite ret_morph in_cons in_nil; case: (x == y).
Qed.

Lemma mem_fail (x : T) : 
  x \in η T Fail = false.
Proof. by rewrite fail_morph_list. Qed.

Lemma mem_alt (x : T) (m n : M T) :
  x \in η T (Alt m n) = (x \in η T m) || (x \in η T n).
Proof. by rewrite alt_morph mem_cat. Qed.

Lemma mem_bindP (s : M T) (k : T -> M T) (y : T) :
  reflect (exists2 x, x \in η T s & y \in η T (k x)) (y \in η T (s >>= k)).
Proof.
  apply /(iffP idP).
  { rewrite bind_morph => /flatten_mapP.
    move => [] l /flatten_mapP [] x xs.
    rewrite mem_seq1 => /eqP -> ymx.
    by exists x. }
  move => [] x xs ymx. rewrite bind_morph.
  apply /flatten_mapP. exists (η T (k x)) => //.
  apply /flatten_mapP. exists x => //. exact: mem_head.
Qed.

End ListMonadMorphismTheory.

Section MFilter.

Import NDMonadMorphism.Syntax.
Import ModelNondet ModelMonad ListMonad Monad_of_ret_bind. 

Context {T : eqType}.
Variable (M : nondetMonad) (η : M ≈> ModelNondet.list).

Definition mfilter (s : M T) (p : pred T) :=
  s >>= (fun a => if p a then Ret a else Fail).

Lemma mem_mfilter (p : pred T) (x : T) (s : M T) :
  (x \in η T (mfilter s p)) = p x && (x \in η T s).
Proof.
  rewrite /mfilter bind_morph /Bind /list /= /Actm /= /Map /bind /=.
  rewrite /ret_component /= /comp. apply /flatten_mapP.
  case: ifP => /andP.
  { move=> [px xs]. exists [:: x]; last exact: mem_head.
    apply /flatten_mapP. exists x => //=.
    by rewrite px ret_morph_list mem_head. }
  move=> H [] l /flatten_mapP [] y ys lh xl.
  move: H => []. case H: (p y).
  { move: lh. rewrite H ret_morph_list mem_seq1 => /eqP ly.
    move: xl. by rewrite ly mem_seq1 => /eqP ->. }
  move: lh. rewrite H fail_morph_list mem_seq1 => /eqP el.
  by rewrite el in xl.
Qed.

End MFilter.

Section ListIdMorphism.

Import NDMonadMorphism.Syntax.
Import ModelNondet ModelMonad ListMonad Monad_of_ret_bind.

Definition id_nattrans : list ~> list :=
  Natural.Pack (Natural.Mixin (@natural_id _)).

Lemma ret_id a : id_nattrans a \o Ret = Ret.
Proof. by []. Qed.

Lemma join_id a m : id_nattrans a (Join m) =
  Join (id_nattrans (list a) ((list # id_nattrans a) m)).
Proof.
  rewrite /id_nattrans /= /bind /list /= /Actm /= /Map /= /ret_component /bind.
  rewrite /comp.
  have: flatten [seq [:: x] | x <- m] = m.
  { by rewrite (flatten_map1 id) map_id. }
  by move=> ->.
Qed.

Definition id_morph : MonadMorphism.Exports.monmorph list list :=
  MonadMorphism.Pack _ _ id_nattrans
    (MonadMorphism.Mixin _ _ id_nattrans ret_id join_id).

Lemma fail_id a : id_morph a Fail = Fail.
Proof. by []. Qed.

Lemma alt_id a m n : id_morph a (m [~] n) = id_morph a m [~] id_morph a n.
Proof. by []. Qed.

Definition id_ndmorph : list ≈> list :=
  NDMonadMorphism.Pack _ _ id_morph
    (NDMonadMorphism.Mixin _ _ id_morph fail_id alt_id).

End ListIdMorphism.
