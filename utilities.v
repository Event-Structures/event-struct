From Coq Require Import Lia Relations.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun eqtype.
From mathcomp Require Import seq path fingraph fintype.


(* TODO: use `valP` from `subType` instead *)
Definition sproof {A : Type} {P : A -> Prop} (e : {x : A | P x}) : P (sval e) := 
  @proj2_sig A P e.

Definition advance {n} (m : 'I_n) (k : 'I_m) : 'I_n :=
  widen_ord (ltnW (ltn_ord m)) k.

Lemma advanceE {n} (m : 'I_n) (k : 'I_m) : 
 advance m k = k :> nat.
Proof. by case: m k => ??[]. Qed.

Arguments advance : simpl never.

Notation none := None.

Notation ord := Ordinal.

Definition comp2 {A B C : Type} (f : B -> B -> A) (g : C -> B) x y := f (g x) (g y).

Notation "f \o2 g" := (comp2 f g) (at level 50) : fun_scope.

(* Set Implicit Arguments. *)
(* Unset Strict Implicit. *)
(* Unset Printing Implicit Defensive. *)

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
Ltac slia := move=> *; ssrnatify; lia.


Notation swap := 
   (ltac:(let f := fresh "_top_" in let s := fresh "_s_" in move=> f s; move: s f)).

Notation apply := (
   ltac: (let f := fresh "_top_" in move=> f {}/f)
).


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

Lemma ltS_neq_lt {n N : nat} : n < N.+1 -> N <> n -> n < N.
Proof. slia. Qed.

Hint Resolve trd_true3 snd_true3 snd_true2 frth_true4 fifth_true5 : core.

Lemma ltn_ind N (P : 'I_N -> Type) :
  (forall (n : 'I_N), (forall (m : 'I_N), (m < n)%N -> P m) -> P n) ->
  forall n, P n.
Proof.
move=> IH n. have [k le_size] := ubnP (nat_of_ord n). 
elim: k n le_size=>// n IHn k le_size. apply/IH=> *. apply/IHn. slia.
Qed.

Ltac ocase := let H := fresh in
  try match goal with  |- context [if ?a is some _ then _ else _] =>
    case H: a; move: H => //=
  end.

(* need that because of inconsistency in Coq stdlib (duplicate name) *)
Notation rtn1_trans := Coq.Relations.Relation_Operators.rtn1_trans.

Lemma crtn1_connectP {n : nat} {r : rel 'I_n} e1 e2:
  reflect (clos_refl_trans_n1 'I_n r e1 e2) (connect r e1 e2).
Proof.
  apply /(iffP idP).
  { move=> /connectP[]. move: e2=> /swap.
    elim /last_ind=> [/=??->//|/= s x IHs]. 
    { apply: rtn1_refl. }
    rewrite rcons_path last_rcons => e2 /andP[/IHs/(_ erefl) ?? ->].
    by apply (@rtn1_trans _ _ _ (last e1 s) x). }
  elim=> [|e3 e4]; first by rewrite connect0.
  move=> HR Hcrtn1 /connectP[s p E].
  apply /connectP. exists (rcons s e4); last first.
  { by rewrite last_rcons. }
  rewrite rcons_path -E. by apply/andP.
Qed.

(* TODO: generalize to `subType` *)
Definition ext {T : Type} {n : nat} (f : 'I_n -> T) : nat -> option T := 
  fun m => omap f (insub m).

Definition inc_ord {n} (m : 'I_n) : 'I_n.+1 := 
  ord (ltnSn n).

Definition dec_ord {n} (m : 'I_n.+1) (neq : n <> m) : 'I_n :=
  ord (ltS_neq_lt (ltn_ord m) neq).

Lemma dec_ordE {n} (m : 'I_n.+1) (neq : n <> m) : 
  dec_ord m neq = m :> nat.
Proof. by case: m neq. Qed.

(* TODO: better names? *)

Definition opred {A : Type} (p : pred A) : pred (option A) :=
  fun ox => if ox is some x then p x else false.

Definition orel {A : Type} (r : rel A) : rel (option A) :=
  fun ox oy => 
    match ox, oy with
    | some x, some y => r x y
    | _     , _      => false
    end.

Lemma opred_ext {A : Type} {n} (p : pred A) (f : 'I_n -> A) : 
  forall m, (p \o f) m -> (opred p \o ext f) m. 
Proof. 
  rewrite /comp /ext /opred. 
  move=> m. case: m.
  move=> m hlt Pm.
  rewrite insubT //.
Qed.

Definition upd {T : nat -> Type} {n}
               (f : forall m : 'I_n, T m) (x : T n) : 
           forall m : 'I_n.+1, T m := 
  fun m => 
    match n =P m :> nat with
    | ReflectT eq  => let 'erefl := eq in x
    | ReflectF neq => f (dec_ord m neq)
    end.

Lemma upd_ord_max {T : nat -> Type} {n} 
                  (f : forall m : 'I_n, T m) (x : T n) :
  upd f x ord_max = x.
Proof.
  rewrite /upd; case: eqP=> /=; last by case.
  by move=> pf; rewrite (eq_irrelevance pf (erefl n)).
Qed.

Lemma upd_lt {T : nat -> Type} {n} 
             (f : forall m : 'I_n, T m) (x : T n) 
             (m : 'I_n.+1) (ltm : m < n) : 
      upd f x m = f (ord ltm).
Proof. 
  rewrite /upd. elim: eqP=> [eq | neq]. 
  { exfalso. slia. }
  rewrite /dec_ord.
  suff: ltS_neq_lt (ltn_ord m) neq = ltm.
  { by move ->. }
  apply /eq_irrelevance.
Qed.

Lemma upd_pred {T : Type} {n} 
               (f : 'I_n -> T) (x : T) (p : pred T) : 
  (p \o f) =1 (p \o upd f x \o inc_ord).
Proof. Admitted.

(* TODO: check that using '_' in `Notation` won't break something *)
(* TODO: generalize notation to partial/total orders? *)
Notation "'_' < n" := ((fun m => m < n) : pred nat) (at level 90).

Lemma upd_ext_pred {T : Type} {n}
               (f : 'I_n -> T) (x : T) (p : pred T) :
  { in _ < n, (opred p \o ext f) =1 (opred p \o ext (upd f x)) }.
Proof. Admitted.

Lemma upd_rel {T : Type} {n} 
              (f : 'I_n -> T) (x : T) (r : rel T) : 
  (r \o2 f) =1 (r \o2 (upd f x \o inc_ord)).
Proof. Admitted.

Lemma upd_ext_rel {T : Type} {n}
                  (f : 'I_n -> T) (x : T) (r : rel T) :
  { in _ < n, (orel r \o2 ext f) =2 (orel r \o2 ext (upd f x)) }.
Proof. Admitted.

Definition is_some {A : Type} : pred (option A) := 
  fun ox => 
    match ox with 
    | some _ => true
    | none   => false
    end.

Definition is_none {A : Type} : pred (option A) := 
  fun ox => 
    match ox with 
    | some _ => false
    | none   => true
    end.

Definition oguard {A : Type} (b : bool) (p : pred A) : pred (option A) :=
  fun ox => if b then odflt false (omap p ox) else is_none ox.

(* Fancy notation for `oguard`-ed dependent sum.
 *
 * `{ x : T | b |- p(x) } === { ox : option T | oguard b (fun x => p(x)) ox}`.
 * 
 * The intuition behind `|-` here is that `oguard` acts a kind of implication.
 *)
Notation "{ x :? T | b |- P }" := 
  (sig (fun ox => oguard b (fun x : T => P) ox))  
    (at level 0, x at level 99) : type_scope.

(* check that notation is working and we didn't break the standard notation *)
Check { x : nat | (x == 1) }.
Check forall x, { y :? nat | x == 1 |- y == 1 }.

Lemma oguard_some {A : Type} {b : bool} {p : pred A} (pf : b) (x : A) (Px : p x) : 
  oguard b p (some x).
Proof. case: b pf=> //=. Qed.

Lemma oguard_none {A : Type} {b : bool} {p : pred A} (pf : ~ b) : 
  oguard b p none.
Proof. case: b pf=> //=. Qed.

Lemma oguard_mapP {A : Type} {b : bool} {p q : pred A} 
                             (f : forall a, p a -> q a) : 
  iforall oa, oguard b p oa -> oguard b q oa. 
Proof. case: b=> [[|]|] //=. Qed.

Lemma oguard_comapB {A : Type} {b b' : bool} {p : pred A} 
                               (h : ~ b' -> forall x, ~ p x)
                               (f : b' -> b) : 
      forall oa, oguard b p oa -> oguard b' p oa.
Proof. 
  rewrite /oguard.
  case: b' h f=> //=.
  { by move=> ? ->. }
  move=> h _ [x|] //=.
  case: b=> [Px|] //=.
  exfalso.
  apply: (h notF x Px).
Qed.

Definition oguardT {A : Type} {p : pred A} {b : bool}
                              (ox : { x :? A | b |- p x })
                              (pf : b) :
           { x: A | p x }.
Proof.
  move: ox pf. case: b=> [[[x|]]|] //=.
  move=> Px _. exact (exist p x Px). 
Qed.

Lemma eqfun_implL {A : Type} {p q : pred A} :
  p =1 q -> forall a, p a -> q a.
Proof. by move=> eqf a; rewrite -(eqf a). Qed.


(* TODO: how do we call this pattern in category theory? *)
(* Lemma oguard_iffB {A : Type} {b b' : bool} {p : pred A}  *)
(*                              (i : b <-> b') : *)
(*       oguard b p =1 oguard b' p.  *)
(* Proof. by rewrite (Bool.eq_true_iff_eq b b' i). Qed.  *)

(* Lemma oguard_mapP_iffB {A : Type} {b b' : bool} {p q : pred A}  *)
(*                                   (f : forall a, p a -> q a)  *)
(*                                   (i : b <-> b') : *)
(*       forall oa, oguard b p oa -> oguard b' q oa.  *)
(* Proof. by move=> oa /(oguard_mapP f oa) /(eqfun_impl (oguard_iffB i) oa). Qed. *)
