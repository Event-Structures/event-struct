From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun eqtype.
From mathcomp Require Import seq path fingraph fintype.
From Coq Require Import Lia.

Notation none := None.

(* ******************************************************************************** *)
(*     Some atomation with Hints, tacticts and iduction scheme                      *)
(* ******************************************************************************** *)

(***** ssrnatlia ******)

(*Transformation of a constraint (x # y) where (x y : nat) and # is a comparison
relation into the corresponding constraint (x #' y) where #' is
the std lib analogue of #. The transformation is performed on the first such formula
found either in the context or the conclusion of the goal *)
Ltac ssrnatify_rel :=
 match goal with
  (* less or equal (also codes for strict comparison in ssrnat) *)
  | H : is_true (leq _ _) |- _ => move/leP: H => H
  | H : context [ is_true (leq ?a ?b)] |- _ =>
     rewrite <- (rwP (@leP a b)) in H
  | |- is_true (leq _ _) => apply/leP
  | |- context [ is_true (leq ?a ?b)] => rewrite <- (rwP (@leP a b))
  (* Boolean equality *)
  | H : is_true (@eq_op _ _ _) |- _ => move/eqP: H => H
  | |- is_true (@eq_op _ _ _) => apply/eqP
  | H : context [ is_true (@eq_op _ _ _)] |- _ =>
     rewrite <-  (rwP (@eqP _ _ _)) in H
  | |- context [ is_true (@eq_op _ ?x ?y)] => rewrite <- (rwP (@eqP _ x y))
  (* Negated boolean equality *)
  | H : is_true (negb (@eq_op _  _ _)) |- _ => move/eqP: H => H
  | |- is_true (negb (@eq_op _  _ _)) => apply/eqP
  | H : context [ is_true (negb (@eq_op _ _ _))] |- _ =>
     rewrite <-  (rwP (@eqP _ _ _)) in H
  | |- context [ is_true (negb (@eq_op _ ?x ?y))] =>
     rewrite <- (rwP (@eqP _ x y))
  | H : (negb (@eq_op _  _ _)) = true |- _ => move/eqP: H => H
  | |- (negb (@eq_op _  _ _)) = true => apply/eqP
  | H : context [ (negb (@eq_op _ _ _)) = true ] |- _ =>
     rewrite <-  (rwP (@eqP _ _ _)) in H
  | |- context [ (negb (@eq_op _ ?x ?y)) = true ] =>
     rewrite <- (rwP (@eqP _ x y))

  | H : (leq _ _) = true |- _ => move/leP: H => H
  | H : context [ (leq ?a ?b) = true] |- _ =>
     rewrite <- (rwP (@leP a b)) in H
  | |- (leq _ _) = true => apply/leP
  | |- context [(leq ?a ?b) = true] => rewrite <- (rwP (@leP a b))
  (* Boolean equality *)
  | H : (@eq_op _ _ _) = true |- _ => move/eqP: H => H
  | |- (@eq_op _ _ _) = true => apply/eqP
  | H : context [(@eq_op _ _ _) = true] |- _ =>
     rewrite <-  (rwP (@eqP _ _ _)) in H
  | |- context [(@eq_op _ ?x ?y) = true] => rewrite <- (rwP (@eqP _ x y))

  (* Negated lt *)
  | H : is_true (negb (leq (S _) _)) |- _ => move: H; rewrite -leqNgt=> H
  | H : context [ is_true (negb (leq (S _) _))] |- _ =>
     rewrite -leqNgt in H
  | |- is_true (negb (leq (S _) _)) => rewrite -leqNgt
  | |- context [ is_true (negb (leq (S _) _))] => rewrite -leqNgt

  (* Negated leq *)
  | H : is_true (negb (leq _ _)) |- _ => move: H; rewrite -ltnNge=> H
  | H : context [ is_true (negb (leq _ _))] |- _ =>
     rewrite -ltnNge in H
  | |- is_true (negb (leq _ _)) => rewrite -ltnNge
  | |- context [ is_true (negb (leq _ _))] => rewrite -ltnNge

   (* = flase *)
  | H : (_ = false) |- _ => move/negbT: H => H
  | |- (_ = false) => apply/negP
  | H : context [ (?a = false)] |- _ =>
     rewrite <-  (rwP (@negP a)) in H
  | |- context [ ?a = false] =>
     rewrite <- (rwP (@negP a))

 end.


(* Converting ssrnat operation to their std lib analogues *)
Ltac ssrnatify_op :=
 match goal with
  (* subn -> minus *)
  | H : context [subn _ _] |- _ => rewrite -!minusE in H
  | |- context [subn _ _] => rewrite -!minusE
  (* addn -> plus *)
  | H : context [addn _ _] |- _ => rewrite -!plusE in H
  | |- context [addn _ _] => rewrite -!plusE
  (* muln -> mult *)
  | H : context [muln _ _] |- _ => rewrite -!multE in H
  | |- context [muln _ _] => rewrite -!multE
 end.

(* Preparing a goal to be solved by lia by translating every formula *)
(* in the context or the conclusion which expresses a constraint on *)
(* some nat into the std lib, Prop, analogues *)
Ltac ssrnatify :=
  repeat progress ssrnatify_rel;
  repeat progress ssrnatify_op.

(* Preprocessing + lia *)
Ltac slia := move=> /=; try (move=> * //=); do [ ssrnatify; lia | exfalso; ssrnatify; lia].

(***** hand made swithes *****)

Notation swap := 
   (ltac:(let f := fresh "_top_" in let s := fresh "_s_" in move=> f s; move: s f)).

Notation apply := (
   ltac: (let f := fresh "_top_" in move=> f {}/f)
).

Notation double := (
  ltac: (let f := fresh "_top_" in move=> f; move: (f) (f)=> {f})
).

Ltac move_anon n :=
  tryif
    lazymatch constr:(n) with
    | S ?n => move=> ?; move_anon n
    | 0 => idtac
    end
  then idtac
  else fail "Too many moves attempted".

Notation "n '$'" :=
  (ltac:(move_anon n))
  (at level 0, only parsing) : ssripat_scope.

(****** Hints to deal with dummy bolean goals ******)

Lemma snd_true3 a b : [|| a, true | b].
Proof. by case: a. Qed.

Lemma trd_true3 a b : [|| b, a | true].
Proof. by case: a; case b. Qed.

Lemma snd_true2 a : a || true.
Proof. by case: a. Qed.

Lemma frth_true4 a b c: [|| a, b, c | true].
Proof. by case: a; case: b; case: c. Qed.

Lemma fifth_true5 a b c d: [|| a, b, c, d | true].
Proof. apply/orP; right. exact: frth_true4. Qed.

Lemma and5P (b1 b2 b3 b4 b5 : bool) :
       reflect [/\ b1, b2, b3, b4 & b5] [&& b1, b2, b3, b4 & b5].
Proof. by apply: (iffP and4P)=> [[->->->/andP[]]|[->->->]]->->. Qed.


Hint Resolve trd_true3 snd_true3 snd_true2 frth_true4 fifth_true5 : core.

(* ******************************************************************************** *)
(*     properties of doamin and codomain of relation                                *)
(* ******************************************************************************** *)

Section DomCodomR.

Context {T : Type} (r : rel T).

Definition rdom x := exists y, r x y.

Definition rcodom x := exists y, r y x.

Definition rfield x := rdom x \/ rcodom x.

Lemma dom_rfield {x y} (_ : r x y) : rfield x.
Proof. by left; exists y. Qed.

Lemma codom_rfield {x y} (_ : r y x) : rfield x.
Proof. by right; exists y. Qed.

End DomCodomR.

Lemma refleqP {a b A B} (rA : reflect A a) (rB : reflect B b) :
  A <-> B -> a = b.
Proof. case=> *; exact /(sameP rA)/(iffP rB). Qed.

Lemma exists_eq {T} {A B : T -> Prop} (_ : forall x, A x <-> B x) : 
  (exists x, A x) <-> exists x, B x.
Proof. split=> [][] x /H ?; by exists x. Qed.

Lemma and_eq (a b c : bool): (a -> (b = c)) -> (a && b = a && c).
Proof. by case: a=> // /(_ erefl) ->. Qed.

Lemma all_in (T : eqType) (s : seq T) x p: all p s -> x \in s -> p x.
Proof.
  elim: s=> //= ?? IHs /andP[? /IHs H]. 
  by rewrite inE=> /orP[/eqP->|/H].
Qed.



