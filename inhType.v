From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order.
From mathcomp Require Import eqtype fingraph path. 
From Coq Require Import ssrsearch.
From event_struct Require Import utilities.

Structure inhType : Type := Inhabitant {type :> eqType; #[canonical(false)] inh : type}.

Arguments inh {_}.

Section Extension.

Variable (T : inhType).
Implicit Types (x : T) (n : nat).

End Extension. 


