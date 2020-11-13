From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype choice.
From mathcomp Require Import eqtype fingraph path order tuple path finmap finfun finset. 
From event_struct Require Import utilities.

(* ************************************************************************* *)
(*     fsfun with relation                                                   *)
(* ************************************************************************* *)

Set Implicit Arguments.
Unset Strict Implicit.

Local Coercion fsval: fset_sub_type >-> Choice.sort.

Open Scope fset_scope.

Structure rfsfun {S : choiceType} {T : eqType}
  (dflt : S -> T) (dom : {fset S}) (r : S -> T -> bool) := 
  Rfsfun {
  f :> {fsfun S -> T for dflt};
  #[canonical(false)] dom_f : finsupp f `<=` dom;
  #[canonical(false)] dep : [forall x : dom, r x (f x)]
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
  {dflt : S -> T} {dom : {fset S}} {r : S -> T -> bool}.
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
  by rewrite -2!fsub1set=> /fsubset_trans/(_ (dom_f t)).
Qed.

(* for each `x \in dom` for `fun_of` function must holds such axiom *)
Lemma axiom_rfsfun x : x \in dom -> r x (t x).
Proof. by move/forallP: (dep t)=> /swap L /(_ [` L]). Qed.

End FunOfrffun.

(* ************************************************************************* *)
(*     Adding element to ftuple                                              *)
(* ************************************************************************* *)

Section AddingElement.

Context {a  : T}. (* this elemnt we want to add to `tupeval` *)
Context {fd : S}. (* fresh element of type T *)

Open Scope fset_scope.

Notation add_f := ([fsfun t with fd |-> a]).

Lemma dep_add : r fd a -> [forall x : fd |` dom, r x (add_f x)].
Proof.
  move=> ?. apply/forallP=> [[/= x /fset1UP[->|/axiom_rfsfun]]].
  - by rewrite fsfun_with.
  rewrite fsfun_withE; by case: ifP=> [/eqP->|].
Qed.

Lemma finsupp_add_f: finsupp add_f `<=` fd |` dom.
Proof.
  rewrite finsupp_with; case: ifP=> ?.
  - exact/(fsubset_trans (fsubD1set _ _))/(fsubset_trans (dom_f t))/fsubsetU1.
  rewrite ![fd |` _]fsetUC; exact: (fsetSU _ (dom_f t)).
Qed.

End AddingElement.

End rfsfunProperties.

Definition add_rfsfun 
  {S : choiceType} {T : eqType} {dflt dom fd a} {r : S -> T -> bool}
  (rafd : r fd a) (t : @rfsfun S T dflt dom r) :=
  Rfsfun (finsupp_add_f t) (dep_add t rafd).

Notation "pf ':::' t" := (add_rfsfun pf t) (at level 20).

Lemma fun_of_add_rffun 
  (S : choiceType) (T : eqType)
  dflt dom (r : S -> T -> bool) (t : rfsfun dflt dom r) a fd
  (rafd : r fd a) x :
  (rafd ::: t) x = if x == fd then a else t x.
Proof.  by rewrite /add_rfsfun fsfun_withE. Qed.
