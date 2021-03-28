From mathcomp Require Import ssrfun.
From monae Require Import hierarchy.

Import Monad.
Local Open Scope monae_scope.

Module MonadMorphism.

Record mixin_of (M N : monad) (η : M ~> N) := Mixin {
  _ : forall a, η a \o Ret = Ret;
  _ : forall a b c (f : a -> M b) (g : b -> M c),
        η c \o (f >=> g) =  (η b \o f) >=> (η c \o g)
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

Module NDMonadMorphism.

Record mixin_of (M N : nondetMonad) (η : M ≈≈> N) := Mixin {
  _ : forall a, η a Fail = Fail;
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