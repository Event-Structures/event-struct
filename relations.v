From Coq Require Import Lia.
From Coq Require Import Relations.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat ssrfun fintype.
From Equations Require Import Equations.
From event_struct Require Import utilities.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section well_founded.

Variable irel : rel nat.

Definition rt_cl : rel nat. Admitted.

Lemma irel_rt_cl : subrel irel rt_cl. Admitted.

Lemma rt_cl_refl: reflexive rt_cl.
Proof. Admitted.

Lemma rt_cl_trans: transitive rt_cl.
Proof. Admitted.

Lemma closureP e1 e2: 
  reflect (clos_refl_trans_n1 _ irel e1 e2) (rt_cl e1 e2).
Proof. Admitted.

End well_founded.

Notation closure := (clos_refl_trans_n1).
