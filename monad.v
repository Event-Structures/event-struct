From mathcomp Require Import ssreflect ssrfun eqtype.
From monae Require Import hierarchy monad_lib.

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

Lemma bind_morph (T : eqType) (M N : monad) (η : M ≈> N) (m : M T) (k : T -> M T) :
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
