From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq path.
From mathcomp Require Import finmap choice eqtype order zify.
From eventstruct Require Import utils order wftype ident.

Open Scope ident_scope.

Lemma ecnode_prop_eq {E : identType} (x y : E): 
  x = y <-> encode x = encode y.
Proof. by split=> [-> //|/encode_inj->]. Qed.


Ltac encode_indets :=
  multimatch goal with
  | E : identType |- context [ ?x == ?y :> ?E ] => 
    lazymatch type of x with 
    | nat => fail
    | _ => rewrite -[x == y](inj_eq encode_inj)
    end
  (* | E : identType *)
  | E : identType |- (?x = _ :> ?E) => 
    lazymatch type of x with 
      | nat => fail
      | _ => try apply/encode_inj
      end
  | E : identType |- context [?x = ?y :> ?E] => 
    lazymatch type of x with 
      | nat => fail
      | _ => rewrite [x = y]ecnode_prop_eq
      end
  | E : identType, H : context [?x = ?y] |- _ => 
    lazymatch type of x with 
      | nat => fail
      | _ => move: H; rewrite [x = y]ecnode_prop_eq=> H
      end
  | E : identType, H : context [?x == ?y :> ?E] |- _ => 
    lazymatch type of x with 
    | nat => fail
    | _ => try rewrite -[x == y](inj_eq encode_inj) in H
    end
  end.

Ltac encodify_once :=
  lazymatch goal with
  (* | E : identType, e := ?x : ?E |- _ => rewrite /e *)
  | |- context [ encode \i0 ] => rewrite ?encode0
  | H : context [ encode \i0 ] |- _ => rewrite ?encode0 in H
  | |- context [ encode \i1 ] => rewrite ?encode1
  | H : context [ encode \i1 ] |- _ => rewrite ?encode1 in H
  | |- context [ encode (fresh _) ] => rewrite ?encode_fresh
  | H : context [ encode (fresh _) ] |- _ => rewrite ?encode_fresh in H
  | |- context [ encode (iter _ fresh _) ] => rewrite ?encode_iter
  | H : context [ encode (iter _ fresh _) ] |- _ => rewrite ?encode_iter in H  
  | |- context [ _ \in nfresh _ _ ] => rewrite ?in_nfresh
  | H : context [ _ \in nfresh _ _ ] |- _ => rewrite ?in_nfresh in H  
  | |- context [ _ <^i _ ] => 
      rewrite ?/(_ <^i _) /= ?/Ident.Def.ident_lt /=
  | H : context [ _ <^i _ ] |- _ => 
      rewrite ?/(_ <^i _) /= ?/Ident.Def.ident_lt /= in H
  | |- context [ _ <=^i _ ] =>
      rewrite ?/(_ <=^i _) /= ?/Ident.Def.ident_le /=
  | H : context [ _ <=^i _ ] |- _ => 
      rewrite ?/(_ <=^i _) /= ?/Ident.Def.ident_le /= in H
  end.

Ltac encodify := repeat progress (encodify_once || encode_indets)=> //=.
Ltac hal := encodify; lia.