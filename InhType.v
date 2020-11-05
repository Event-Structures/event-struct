From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order.
From mathcomp Require Import eqtype fingraph path. 
From event_struct Require Import utilities.

Structure inhType : Type := Inhabitant {type :> Type; #[canonical(false)] inh : type}.

Implicit Type T : inhType.

Section Extension.

Context {T : inhType}.
Implicit Types (x : T) (n : nat).
Notation inh := (inh T).

Definition ext {n} (f : 'I_n -> T) (k : nat) : T := oapp f inh (insub k).

Lemma ext_add {x n} {f : 'I_n -> T} r : r != n ->
  ext (add f x) r = ext f r.
Proof.
  rewrite /ext. do ?case: insubP; try slia. move=> ?? <- [/= ??? /double ?<-?].
  rewrite add_lt //=; try slia. move=> ?/=. exact /congr1 /ord_inj.
Qed.

Lemma ext_add_n  {x n} {f : 'I_n -> T} :
  ext (add f x) n = x.
Proof. 
  rewrite /ext. case: insubP; try slia. move=> [/=] ? L _ /esym E.
  case: _ / E L=> ?. by rewrite add_ord_max.
Qed. 

Lemma pred_ext {n} (f : 'I_n -> T) (p : pred T) (r : 'I_n) :
 p (ext f r) = p (f r).
Proof.
  case: r=> /= *. rewrite /ext. case: insubP=> //= [*|]; try slia.
  exact /congr1 /congr1 /ord_inj.
Qed.

Lemma rel_ext {n x} (f : 'I_n -> T) (r : rel T) (a b : nat) :
   ~ (rfield r inh) -> (relpre (ext f) r) a b -> (relpre (ext (add f x)) r) a b.
Proof.
  rewrite /relpre=> H /=. case L: (a < n).
  { rewrite ext_add //; try slia.
    case L': (b < n). 
    { rewrite ext_add //. slia. }
    rewrite {2}/ext. do ?case: insubP; try slia.
    by move/1$/(codom_rfield _). }
  rewrite {1}/ext. do ?case: insubP; try slia. 
  by move/1$/(dom_rfield _).
Qed.
 
End Extension.


