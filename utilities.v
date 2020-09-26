From Coq Require Import Lia Relations.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun eqtype.
From mathcomp Require Import seq path fingraph fintype.


Definition sproof {A : Type} {P : A -> Prop} (e : {x : A | P x}) : P (sval e) := 
  @proj2_sig A P e.

Definition advance {n} (m : 'I_n) (k : 'I_m) : 'I_n :=
  widen_ord (ltnW (ltn_ord m)) k.

Arguments advance : simpl never.

Lemma advanceE {n} (m : 'I_n) (k : 'I_m) : 
 advance m k = k :> nat.
Proof. by case: m k => ??[]. Qed.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
Ltac slia := move=> * //; ssrnatify; lia.


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

Lemma ltS_neq_lt {n N : nat}: (n < N.+1 -> N <> n -> n < N)%N.
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

Ltac dep_case := 
  match goal with  |- context [if ?a as _ return (_) then _ else _] =>
    case: {2}a {-1}(@erefl _ a) erefl=> {2 3}->
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

Section opt_fun.

Definition ord_dom_to_nat {N T T'} 
  (f : 'I_N -> T) (h : T -> option T') (n : nat) : option T' := 
  (match n < N as L return (n < N = L -> _) with
   | true  => fun pf => h (f (Ordinal pf))
   | false => fun=> None
   end erefl).

Definition ord_f_to_nat {N M} (k : nat) (f : 'I_N -> 'I_M) (n : nat) : nat :=   
  (match n < N as L return (n < N = L -> _) with
   | true  => fun pf => nat_of_ord (f (Ordinal pf))
   | false => fun=> k + n
end erefl).

Lemma opt_comp {T1 T2 T3} (f : T1 -> T2) (g : T2 -> T3) y : 
  omap (fun z => g (f z)) y = (omap g) ((omap f) y).
Proof. move: y. by case. Qed.

Context {T T' T1 T2 T3 : Type} {N M K : nat}.

Lemma inj_ord_dom_to_nat (k : 'I_N)
  {f1 f2: 'I_N -> T} (h : T -> option T') :
  injective h -> 
  ord_dom_to_nat f1 h k = ord_dom_to_nat f2 h k -> f1 k = f2 k.
Proof.
move=> Ih. rewrite {1}/ord_dom_to_nat.
case: {2}(k < N) {-1}(@erefl _ (k < N)) erefl=> {2 3}->;
rewrite/ord_dom_to_nat=> L;
case: {2}(k < N) {-1}(@erefl _ (k < N)) erefl=> {2 3}-> L'//.
- move/Ih. have->: Ordinal L = k by apply/ord_inj.
by have->: Ordinal L' = k by apply/ord_inj.
1,2: by exfalso; rewrite L in L'.
case: k L {L'}=>/= m L. by rewrite L.
Qed.

Lemma opt_can {f : T -> T'} {g : T' -> T}: 
  cancel f g -> cancel (omap f) (omap g).
Proof. move=> c []//=?. by rewrite c. Qed.

Lemma opt_inj {A B} (f : A -> B): injective f -> injective (omap f).
Proof. by move=> I [?[]//=?[/I->]|[]//]. Qed.

Lemma eq_opt {f g : T -> T'}: f =1 g -> omap f =1 omap g.
Proof. move=> E []//=?. by apply/congr1/E. Qed.

Definition onat_eq_ord {N M} (n : option 'I_N) (m : option 'I_M) :=
  (omap (@nat_of_ord N)) n == (omap (@nat_of_ord M)) m.

Lemma ord_f_to_natE k (f : 'I_N -> 'I_M) (i : 'I_N) :
  f i = (ord_f_to_nat k f) i :> nat.
Proof.
rewrite/ord_f_to_nat.
case: {2}(i < N) {-1}(@erefl _ (i < N)) erefl=> {2 3}->.
- move=> ?. by apply/congr1/congr1/ord_inj.
case: i=> ?/= E. by rewrite E.
Qed.

Lemma ord_f_to_nat_Nlt k (f : 'I_N -> 'I_M) n: 
  (n < N = false) -> ord_f_to_nat k f n = k + n.
Proof.
move=> LnN. rewrite/ord_f_to_nat.
by case: {2}(n < N) {-1}(@erefl _ (n < N)) erefl=> {2 3}-> E; first 
by rewrite E in LnN.
Qed.

Lemma ord_dom_to_nat_le (f : 'I_N -> option 'I_M) n k: 
  some k = (ord_dom_to_nat f (omap (@nat_of_ord M))) n -> k < M.
Proof.
rewrite/ord_dom_to_nat.
case: {2}(n < N) {-1}(@erefl _ (n < N)) erefl=> {2 3}-> // nN.
rewrite/omap. by case: (f (Ordinal nN))=> // a [->].
Qed.

Lemma ord_dom_to_nat_comp 
  (f : 'I_M -> T) (g : 'I_N -> 'I_M) (h : T -> option T'):
  (ord_dom_to_nat f h) \o (ord_f_to_nat (M - N) g) =1 ord_dom_to_nat (f \o g) h.
Proof.
move=> k/=. rewrite /ord_dom_to_nat. do ?dep_case=>//=.
- move=> L ?. apply/congr1/congr1/ord_inj=>/=. rewrite/ord_f_to_nat. dep_case.
- move=> ?. by apply/congr1/congr1/ord_inj. by rewrite L.
- rewrite/ord_f_to_nat=>LkN H. exfalso. move: H.
  case: {2}(k < N) {-1}(erefl (k < N)) erefl=> {2 3}-> //=; first by
  move=> LnNt; rewrite LnNt in LkN.
- slia.
rewrite/ord_f_to_nat=>LkN H. exfalso. move: H.
case: {2}(k < N) {-1}(erefl (k < N)) erefl=> {2 3}-> //=; last by
move=> LnNt; rewrite LnNt in LkN. move=> e. by case: (g (Ordinal _))=>/=?->.
Qed.

Lemma ord_dom_to_nat_eq
  {f1 f2 : 'I_M -> T} {h : T -> option T'} :
  f1 =1 f2 -> ord_dom_to_nat f1 h =1 ord_dom_to_nat f2 h.
Proof.
move=> Ef k. rewrite {1}/ord_dom_to_nat.
case: {2}(k < M) {-1}(erefl (k < M)) (erefl (k < M))=> {2 3}->; 
rewrite /ord_dom_to_nat=> e; 
case: {2}(k < M) {-1}(erefl (k < M)) (erefl (k < M))=> {2 3}->=>//.
- move=> ?. apply/congr1. rewrite Ef. by apply/congr1/ord_inj.
- by rewrite e.
move=> E. by rewrite E in e.
Qed.

Lemma ord_dom_to_nat_opt_comp t
  (f : 'I_N -> 'I_M) (g : 'I_N -> option 'I_N):
  ord_dom_to_nat (omap f \o g) (omap (@nat_of_ord M)) =1
  (omap (ord_f_to_nat t f) \o
  ord_dom_to_nat g (omap (@nat_of_ord N))).
Proof.
move=> k. rewrite {1}/ord_dom_to_nat/=.
case: {2}(k < N) {-1}(erefl (k < N)) erefl=> {2 3}->;
rewrite/ord_dom_to_nat=> L;
case: {2}(k < N) {-1}(erefl (k < N)) erefl=> {2 3}-> L'//; rewrite -?opt_comp.
- have->: (Ordinal L) = (Ordinal L') by apply/ord_inj.
  case: (g (Ordinal L'))=> //= ?. apply/congr1. exact: ord_f_to_natE.
all: exfalso; by rewrite L in L'.
Qed.

Lemma onat_eq_ord_widen_ord
  (n : option 'I_N) (L : N <= M) (k : option 'I_K) :
  onat_eq_ord ((omap (id \o widen_ord L)) n) k = 
  onat_eq_ord n k.
Proof. by case: n. Qed.

Hint Resolve eqxx : core.

End opt_fun.

Theorem inj_le_card {T T' : finType} (f : T -> T'): 
  injective f -> #|T| <= #|T'|.
Proof. move=> /card_codom<-. by rewrite max_card. Qed.
