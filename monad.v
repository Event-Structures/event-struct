From mathcomp Require Import ssreflect ssrfun eqtype.
From monae Require Import hierarchy monad_lib.

Import Monad.
Local Open Scope monae_scope.

Module MonadMorphism.
Record mixin_of (M N : monad) (η : M ~> N) := Mixin {
  _ : forall a, η a \o Ret = Ret;
  _ : forall a (m : M (M a)),
        η a (Join m) = Join (η (N a) ((M # (η a)) m))
}.
Structure type (M N : monad) := Pack
  { cpmm : M ~> N ; class : mixin_of M _ cpmm }.
Module Exports.
Notation monmorph := type.
Coercion cpmm : type >-> Natural.type.
Notation "f ≈≈> g" := (monmorph f g) (at level 1) : monae_scope.
Notation MonadMorphism p := (Pack (Mixin p)).
End Exports.
End MonadMorphism.
Export MonadMorphism.Exports.

Lemma ret_mon (M N : monad) (η : M ≈≈> N) :
  forall a, η a \o Ret = Ret.
Proof. case: η => cpmm; by case. Qed.

Lemma join_mon (M N : monad) (η: M ≈≈> N) :
  forall a (m : M (M a)),
    η a (Join m) = Join (η (N a) ((M # (η a)) m)).
Proof. case: η => cpmm; by case. Qed.

Module NDMonadMorphism.
Record mixin_of (M N : nondetMonad) (η : M ≈≈> N) := Mixin {
  _ : forall a, η a Fail = Fail;
  _ : forall a m n, η a (Alt m n) = Alt (η a m) (η a n)
}.
Structure type (M N : nondetMonad) := Pack
  { cpmm : M ≈≈> N ; class : mixin_of M _ cpmm }.
Module Exports.
Notation monmorph := type.
Coercion cpmm : type >-> MonadMorphism.type.
Notation "f ≈> g" := (monmorph f g) (at level 1) : monae_scope.
Notation MonadMorphism p := (Pack (Mixin p)).
End Exports.
End NDMonadMorphism.
Export NDMonadMorphism.Exports.

Lemma ret_ndmon (M N : nondetMonad) (η : M ≈> N) :
  forall a, η a \o Ret = Ret.
Proof. case: η => cpmm; case: cpmm => cpmm; by case. Qed.

Lemma join_ndmon (M N : nondetMonad) (η: M ≈> N) :
  forall a (m : M (M a)),
    η a (Join m) = Join (η (N a) ((M # (η a)) m)).
Proof. case: η => cpmm; case: cpmm => cpmm; by case. Qed.

Lemma fail_ndmon (M N : nondetMonad) (η: M ≈> N) :
  forall a, η a Fail = Fail.
Proof. case: η => cpmm; by case. Qed.

Lemma alt_ndmon (M N : nondetMonad) (η: M ≈> N) :
  forall a m n, η a (Alt m n) = Alt (η a m) (η a n).
Proof. case: η => cpmm; by case. Qed.

Lemma in_bind (T : eqType) (M N : monad) (η : M ≈≈> N) (m : M T) (k : T -> M T) :
  η T (m >>= k) = (η T m) >>= (fun x => η T (k x)).
Proof.
  rewrite /Bind join_mon.
  have: (M # η T) ((M # k) m) = (M # (η T \o k)) m.
  { by rewrite monad_lib.fmap_oE. }
  move=> ->.
  have: η (N T) ((M # (η T \o k)) m) = (η (N T) \o (M # (η T \o k))) m.
  { done. }  
  move=> ->. rewrite -natural. done.
Qed.

