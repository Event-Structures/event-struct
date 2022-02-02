From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq path.
From mathcomp Require Import finmap choice eqtype order zify.
From eventstruct Require Import utils order wftype ident.

Open Scope ident_scope.

Lemma ecnode_prop_eq {E : identType} (x y : E) :
  x = y <-> encode x = encode y.
Proof. by split=> [-> //|/encode_inj->]. Qed.

Ltac encode_indets :=
  multimatch goal with
  | E : identType |- context [@eq_op ?E ?x ?y ] => 
    lazymatch type of x with 
    | nat => fail
    | _ => rewrite -[x == y](inj_eq encode_inj)
    end
  | E : identType |- (@eq ?E ?x _) => 
    lazymatch type of x with 
    | nat => fail
    | _ => try apply/encode_inj
    end
  | E : identType |- context [@eq ?E ?x ?y] => 
    lazymatch type of x with 
    | nat => fail
    | _ => rewrite [x = y]ecnode_prop_eq
    end
  | E : identType, e := _ |- _ => 
    lazymatch type of e with 
    | ?E => rewrite ?/e
    end
  end.

Lemma le_identE {E : identType} (e1 e2 : E) : 
  e1 <=^i e2 = (encode e1 <= encode e2).
Proof. by []. Qed.

Lemma lt_identE {E : identType} (e1 e2 : E) : 
  e1 <^i e2 = (encode e1 < encode e2).
Proof. by []. Qed.

Open Scope type_scope.

Definition identE {E : identType} := 
  (@encode0 E, @encode1 E, @encode_fresh E, @encode_iter E, 
   @in_nfresh E, @le_identE E, @lt_identE E).

Ltac push_ident_context := (
  match goal with
  | H : context [ encode \i0 ] |- _ => move: H; try clear H
  | H : context [ encode \i1 ] |- _ => move: H; try clear H
  | H : context [ encode (fresh _) ] |- _ => move: H; try clear H
  | H : context [ encode (iter _ fresh _) ] |- _ => move: H; try clear H
  | H : context [ _ \in nfresh _ _ ] |- _ => move: H; try clear H
  | H : context [ _ <=^i _ ] |- _ => move: H; try clear H
  | H : context [ _ <^i _ ] |- _ => move: H; try clear H
  | E : identType, H : context [@eq_op ?E ?x _] |- _ => move: H; try clear H
  | E : identType, H : context [@eq ?E ?x _] |- _ => move: H; try clear H
  end).

Ltac encodify := (repeat progress push_ident_context); (repeat progress encode_indets); rewrite ?identE //=.

Ltac ilia  := encodify; lia.