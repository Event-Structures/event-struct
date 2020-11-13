From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order.
From mathcomp Require Import eqtype fingraph path. 
From event_struct Require Import utilities.

Structure inhType : Type := Inhabitant {type :> eqType; #[canonical(false)] inh : type}.

Arguments inh {_}.


