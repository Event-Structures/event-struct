From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype choice.
From mathcomp Require Import eqtype fingraph path order tuple path finmap finfun finset. 
From event_struct Require Import utilities.

(******************************************************************************)
(* This file contains the definitions of:                                     *)
(*           rfsfun dflt dom r  == that a function that defined on subset of  *)
(*                            dom and behaives like dflt function out of it's *)
(*                            domain. Also we requre that it's restriction    *)
(*                            on dom (as a relation) should be a subrelation  *)
(*                            of r                                            *)
(*           rfsfun_i rr' ffr == if we've got `ffr : rfsfun dflt dom r` and   *)
(*                           rr' -- proof that r x (f x) implies r' x (f x)   *)
(*                           on all elements from dom than we can obtain a    *)
(*                           new rfsfun of type `rfsfun dflt dom r'`          *)
(*           add_rsfufn fd a pf ffr == if we have some                        *)
(*                                 `ffr : rfsfun dflt dom r` and pf -- proof  *)
(*                                 of `r fd a` we can extand out ffr on one   *)
(*                                 element fd and bind in to a                *)
(******************************************************************************)

(* ************************************************************************* *)
(*     fsfun with relation                                                   *)
(* ************************************************************************* *)

Set Implicit Arguments.
Unset Strict Implicit.

Local Coercion fsval: fset_sub_type >-> Choice.sort.

Open Scope fset_scope.

Structure rfsfun {S : choiceType} {T : eqType}
  (dflt : S -> T) (dom : seq S) (r : S -> T -> bool) := 
  Rfsfun {
  f                         :> {fsfun S -> T for dflt};
  #[canonical(false)] dom_f : [forall x : finsupp f, (fsval x) \in dom];
  #[canonical(false)] dep   : all (fun x => r x (f x)) dom;
}.
(* For example if we take                                                    *)
(* dom := 0,...,n                                                            *)
(* r := <=                                                                   *)
(* then `rfsfun id dom =>` r will be a finite function wich for every element*)
(* from `S` gives an element from `T` that is not smaller that the fisrt one.*) 
(* In general `rfsfun dflt dom =>`` corresponds to the function wich takes   *)
(* `x : T` and if `x \in dom` it returns element s.t. `r x (f x)`,           *)
(* and `dflt x` else                                                         *)

Section rfsfunProperties.

Context {n : nat} {S : choiceType} {T : eqType}
  {dflt : S -> T} {dom : seq S} {r : S -> T -> bool}.
Variable t : rfsfun dflt dom r.

(* ************************************************************************* *)
(*     Function of rffun                                                     *)
(* ************************************************************************* *)

Section FunOfrffun.

Lemma memNdom x: x \notin dom -> t x = dflt x.
Proof.
  move /negP=> D.
  apply/eqP; rewrite -memNfinsupp; apply/negP.
  move=> I; apply/D; move: I.
  by move/forallP: (dom_f t)=> /swap L /(_ [` L]).
Qed.

(* for each `x \in dom` for `fun_of` function must holds such axiom *)
Lemma axiom_rfsfun x : x \in dom -> r x (t x).
Proof. by move/allP: (dep t)=> /apply. Qed.

End FunOfrffun.

(* ************************************************************************* *)
(*     Adding element to ftuple                                              *)
(* ************************************************************************* *)

Section AddingElement.

Context {a  : T}. (* this elemnt we want to add to `tupeval` *)
Context {fd : S}. (* fresh element of type T *)

Open Scope fset_scope.

Notation add_f := ([fsfun t with fd |-> a]).

Lemma dep_add : r fd a -> all (fun x => r x (add_f x)) (fd :: dom).
Proof.
  move=> ?; apply/allP=> ?.
  rewrite ?inE fsfun_withE.
  by case: ifP=> /= [/eqP-> //| ? /(allP (dep t))].
Qed.

Lemma finsupp_add_f: [forall x : finsupp add_f, (fsval x) \in fd :: dom].
Proof.
  apply/forallP=> [[/= ?]]. 
  rewrite finsupp_with /= ?inE.
  case: ifP=> [? /fsetD1P[? L]|? /fset1UP[->| L]];
  by rewrite ?eq_refl // (forallP (dom_f t) [` L]).
Qed.

End AddingElement.

Context {r' : S -> T -> bool} 
        (rr' : all (fun x => r x (t x) ==> r' x (t x)) dom).

Lemma dep_r': all (fun x => r' x (t x)) dom.
Proof.
  apply/allP.
  by move/allP: rr'=> H ? /dup I /H /implyP /(_ (allP (dep t) _ I)).
Qed.

Definition rfsfun_impl := Rfsfun (dom_f t) (dep_r').

End rfsfunProperties.

Definition add_rfsfun 
  (S : choiceType) (T : eqType) dflt dom (r : S -> T -> bool) fd a
  (rafd : r fd a) (t : @rfsfun S T dflt dom r) :=
  Rfsfun (finsupp_add_f t) (dep_add t rafd).

Arguments add_rfsfun {_ _ _ _ _}.

Notation "pf ':::' t" := (add_rfsfun _ _ pf t) (at level 20).

Lemma fun_of_add_rffun 
  (S : choiceType) (T : eqType)
  dflt dom (r : S -> T -> bool) (t : rfsfun dflt dom r) a fd
  (rafd : r fd a) x :
  (rafd ::: t) x = if x == fd then a else t x.
Proof.  by rewrite /add_rfsfun fsfun_withE. Qed.