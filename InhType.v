From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order.
From mathcomp Require Import eqtype fingraph path. 
From event_struct Require Import utilities.

Structure inhType : Type := Inhabitant {type :> Type; #[canonical(false)] inh : type}.

Implicit Type T : inhType.

Section Extension.

Context {T : inhType}.
Implicit Types (x : T) (n : nat).
Notation inh := (inh T).

Definition ext {n} (f : 'I_n -> T) : nat -> T := fun k =>
  if insub_ord n k is some k then f k else inh.

Lemma ext_add {x n} {f : 'I_n -> T} r : r != n ->
  ext (add f x) r = ext f r.
Proof.
  rewrite /ext. insub_case=> ??; insub_case=> //; try slia.
  move => L. rewrite add_lt. exact /congr1 /ord_inj.
Qed.

Lemma ext_add_n  {x n} {f : 'I_n -> T} :
  ext (add f x) n = x.
Proof. rewrite /ext. insub_case=> *; try slia. by rewrite add_ord_max. Qed.

Lemma pred_ext {n} (f : 'I_n -> T) (p : pred T) (r : 'I_n) :
 p (ext f r) = p (f r).
Proof.
  case: r=> /= *. rewrite /ext. insub_case=> [?|]; try slia.
  exact /congr1 /congr1 /ord_inj.
Qed.


Lemma rel_ext {n x} (f : 'I_n -> T) (r : rel T) (a b : nat)
  (dv_not_in_r : ~ (rfield r inh)) :
  (r \o2 ext f) a b -> (r \o2 ext (add f x)) a b.
Proof.
  rewrite /comp2. case L: (a < n).
  { rewrite ext_add //; try slia.
    case L': (b < n). 
    { rewrite ext_add //. slia. }
    rewrite {2}/ext. insub_case=> [? _|_/(codom_rfield r)]; slia. }
  rewrite {1}/ext. insub_case=> [? _|_/(dom_rfield r)]; slia.
Qed.

End Extension.


