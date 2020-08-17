From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
Ltac ssrnatlia := ssrnatify; lia.
