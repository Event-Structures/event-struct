From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype.
From mathcomp Require Import eqtype fingraph path order tuple path. 
From event_struct Require Import utilities.

(* ************************************************************************* *)
(*     Functional Tuples                                                     *)
(* ************************************************************************* *)


Structure ftuple (n : nat) {T : eqType} (dom : n.-tuple T) (r : rel T) := 
  DTuple {
  codom :> n.-tuple T; 
  #[canonical(false)] dep : all2 r codom dom
}.
(* For example if we take                                                    *)
(* dom := 0,...,n                                                            *)
(* r := <=                                                                   *)
(* then `ftuple n dom` r will be a tuple with each element not bigger than   *)
(* number of it position (such ftuple can code fpred funtion)                *)
(* In general `ftuple n dom r` corresponds to the function wich takes        *)
(* `x : T` and if `x \in dom` it returns element with the same index in      *)
(* `tupeval`, and `x` else (look at `fun_of` and `axiom_fun_of`)             *)
(* Note: this version models only endofunctions                              *)

Canonical ftuple_subType 
  n T dom r
   := Eval hnf in [subType for (@codom n T dom r)].

Section ftupleProperties.

Notation "x ':t:' y" := (cons_tuple x y) (at level 0).

Context {n : nat} {T : eqType} {dom : n.-tuple T} {r : rel T}.
Variable t : ftuple n dom r.

Lemma size_ftuple: size t = size dom.
Proof. case: t=> /= *. by rewrite !size_tuple. Qed.

(* ************************************************************************* *)
(*     Function of ftuple                                                    *)
(* ************************************************************************* *)

Section FunOfftuple.

(* TODO: make as coercion *)
(* `fun_of` constructs function corresponding to `t : ftuple n dom r` *)
Definition fun_of x : T := nth x t (index x dom).

Lemma fun_of_notin x: x \notin dom -> fun_of x = x.
Proof.
  rewrite /fun_of=> /memNindex ->. by rewrite nth_default // size_ftuple.
Qed.

Lemma axiom_fun_of x : x \in dom -> r (fun_of x) x.
Proof. 
  rewrite /fun_of=> ?. case: t => tp /=. rewrite all2E=> /andP[E /all_in H].
  apply /(H (nth x tp (index x dom), x)) /(nthP (x, x)). exists (index x dom).
  { by rewrite (eqP (zip_tupleP _ _)) -{2}(size_tuple dom) index_mem. }
  rewrite nth_zip ?(eqP E) //. exact/congr1/nth_index.
Qed.

End FunOfftuple.

(* ************************************************************************* *)
(*     Adding element to ftuple                                              *)
(* ************************************************************************* *)

Section AddingElement.

(* the elemnt we want to add to `tupeval` *)
Context {a  : T}.
(* fresh element of type T *)
Context {fd : T}. 

Lemma dep_add : r a fd -> all2 r (a :t: t) (fd :t: dom).
Proof. move=>/=->. by rewrite dep. Qed.

End AddingElement.

End ftupleProperties.

Canonical cons_ftuple {T : eqType} {n dom ns a} {r : rel T}
  (rafd : r a ns) (t : @ftuple n T dom r) :=
  DTuple _ _ _ _ _ (dep_add t rafd).

Notation "pf ':ft:' t" := (cons_ftuple pf t) (at level 20).

Coercion fun_of: ftuple >-> Funclass.

Lemma fun_of_cons_tuple
  n (T : eqType) dom (r : rel T) (t : ftuple n dom r) a fd
  (rafd : r a fd) x:
  (rafd :ft: t) x = if x == fd then a else t x.
Proof. 
  rewrite /fun_of /cons_tuple /= eq_sym.
  by case: ifP. 
Qed.