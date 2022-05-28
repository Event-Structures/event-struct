From RelationAlgebra Require Import lattice monoid rel kat_tac kat kleene.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice.
From eventstruct Require Import utils rel_algebra.

(*****************************************************************************)
(* exlaberal theory of rewriting systems                                     *)
(* inspired by "Term Rewriting and All That"                                 *)
(* Fisrt section called Commutation. Here the theory of exlaberal rewriting  *)
(* systems with two rewriting rules derived:                                 *)
(* We define several properties of rewriting systems and prove some          *)
(* relationships between them                                                *)
(*   diamond_commute (~>) (>>) == ∀ s1 s2 s3                                 *)
(*                              s1 ~> s2                                     *)
(*                              v     v                                      *)
(*                              v     v                                      *)
(*                              s3 ~> s4 - exists                            *)
(*                                                                           *)
(*   strong_commute (~>) (>>)           == ∀ s1 s2 s3                        *)
(*                              s1 ~> s2                                     *)
(*                              v     v                                      *)
(*                              v     v                                      *)
(*                              ⋮    ⋮                                     *)
(*                              v     v                                      *)
(*                              v     v                                      *)
(*                              s3 ~> s4 - exists                            *)
(*   commute (~>) (>>)                  == ∀ s1 s2 s3                        *)
(*                              s1 ~>  ...  ~> s2                            *)
(*                              v              v                             *)
(*                              v              v                             *)
(*                              ⋮             ⋮                            *)
(*                              v              v                             *)
(*                              v              v                             *)
(*                              s3 ~>  ...  ~> s4 - exists                   *)
(*   diamond_confluent (~>)              == diamond_commute (~>) (~>)        *)
(*   confluence   (~>)                   == commute (~>) (~>)                *)
(*   dcomm_comm                          <-> commuting_diamond_prop (~>) (>>)*)
(*                                       implies commute (~>) (>>)           *)
(*   dconfl_confl                        <-> diamond_confluent (~>) implies  *)
(*                                       confluence (~>)                     *)
(* In the EqvRewriting we have the exlaberal theory of the rewriting system  *)
(* with some equivalence relation.                                           *)
(* eqv_diamond_confluent (~>) (~~) == version of the diamond property for    *)
(*                         the rewriting systems with equivalence: it states *)
(*                         that s1 ~> s2 and s1 ~> s3 implies existance of   *)
(*                         some s4 and s4' s.t. s2 ~> s4, s3 ~> s4' and      *)
(*                         s4 ~~ s4'.                                        *)
(*   eqv_confluent (~>) (~~)       == the confluence principle for the       *)
(*                         rewriting systems with an equivalence relation:   *)
(*             s1 ~>⁺ s2 |                                                   *)
(*                       | ==> exists s4 ~~ s4' s.t. s2 ~>⁺ s4 and s3 ~>⁺ s4'*)
(*             s1 ~>⁺ s3 |                                                   *)
(*   confl_eqv                     <-> diamond_commute (~>) (~~) with        *)
(*                         eqv_diamond_confluent (~>) (~~) implies           *)
(*                         eqv_confluent (~>) (~~)                           *)
(* In the EqvLabRewriting we proved the analogue of Commuation Union Lemma   *)
(* Originally this lemma states that if one have two relations ~> and >> and *)
(* they statisfy diamond_commute (~>) (>>), then (~> ∪ >>) is confluent.     *)
(* But want to exlaberalize this lemma in two steps:                         *)
(*   1) let us have an arbitrary number of relations -- we model it by       *)
(*      consindering one labeling relation: r : L -> hrel S S, where L is an *)
(*      arbitrary label Type                                                 *)
(*   2) let us parametrize this lemma with some equivalence relation         *)
(* Let L and S be some types and r : L -> hrel S S                           *)
(* eqv_diamond_commute (~>) (>>) (~~) == version of the diamond property for *)
(*                       the rewriting systems with equivalence: it states   *)
(*                       that s1 ~> s2 and s1 ~> s3 implies existance of     *)
(*                       some s4 and s4' s.t. s2 ~> s4, s3 ~> s4' and        *)
(*                       that s1 ~> s2 and s1 >> s3 implies existance of     *)
(*                       some s4 and s4' s.t. s2 ~> s4, s3 >> s4' and        *)
(*                       exlab r s1 s2 == ∃ l, s.t. r l s1 s2 holds          *)
(*            eqv_diamoind_commute r e <-> if forall two labels l₁ l₂ we now *)
(*                       that eqv_diamond_commute (r l1) (r l2) (~~) and     *)
(*                       diamond_commute (exlab r) (~~) than exlab r is      *)
(*                       conluent w.r.t (~~) i.e eqv_confluent (exlab r) (~~)*)
(* Consider we have some labeled relation r (statisfying all properties      *)
(* above), and some equivalence ~~. If r has type L -> hrel S S, and T is a  *)
(* S's subType, forall relation rel : hrel S S we can define                 *)
(*                       sub rel == contranction of rel to the sub-type T    *)
(* so clearly we can define a labeled rewriting system with an equivalence   *)
(* relation structure on T (with relations `sub ∘ r` and `sub (~~)`).        *)
(* The question is: when such subsystem is confluent? In the SubRewriting    *)
(* section we are trying to answer on this question.                         *)
(* Let T : subType p, for some p : pred S, with s1, s2,... we will denote the*)
(* variables of type S, and with t1, t2,... we will denote the variables     *)
(* of type T                                                                 *)
(*          eqv_restpect_p (~~) <-> if t ~~ s then p s holds                 *)
(*          r_respects_p   (r)  <-> if for some labels l1, l2, r l2 t1 t2,   *)
(*                        r l1 t1 t3, then for all s s.t. r l2 t3 s we have  *)
(*                        that p s holds                                     *)
(*    sub_eqv_comm_union r (~~) <-> it two properties above holds than       *)
(*                        eqv_confluent (exlab (sub ∘ r)) (sub ~~)           *)
(*****************************************************************************)

Local Open Scope rel_scope.

Section Commutation.

Context {S : Type} (r1 r2 : hrel S S).

Definition diamond_commute := forall s1 s2 s3,
  r1 s1 s2 -> r2 s1 s3 -> exists2 s4, r2 s2 s4 & r1 s3 s4.

Definition strong_commute := forall s1 s2 s3,
  r1 s1 s2 -> r2^+ s1 s3 -> exists2 s4 : S, r2^+ s2 s4 & r1 s3 s4.

Definition commute := forall s1 s2 s3,
  r1^+ s1 s2 -> r2^+ s1 s3 -> exists2 s4, r2^+ s2 s4 & r1^+ s3 s4.

Lemma dcomm_scomm :
  diamond_commute -> strong_commute.
Proof.
  move=> diamond s1 s2 s3 + str; move: str s2.
  suff: (r2^+ \<= (fun s1 s3 => forall s2 : S, r1 s1 s2 -> exists2 s4 : S, r2^+ s2 s4 & r1 s3 s4)).
  - exact.
  apply/itr_ind_l1=> {s1 s3} [?? /diamond d ? /d[x /(itr_ext r2) *]|s1 s3 /=].
  - by exists x.
  move=> [? /diamond d IH ? /d[x ? /IH[y *]]]; exists y=> //.
  apply/(itr_cons r2); by exists x.
Qed.

Lemma dcomm_comm :
  diamond_commute -> commute.
Proof.
  move=> d s1 s2 s3.
  move: s3=> /[swap].
  suff: (r1^+ \<= (fun s1 s2 => forall s3, r2^+ s1 s3 -> exists2 s4, r2^+ s2 s4 & r1^+ s3 s4)).
  - exact.
  apply/itr_ind_l1=> {s1 s2} [?? s ? |s1 s2 /= [s5 /(dcomm_scomm d) c IH s3 /c]].
  - case/(dcomm_scomm d _ _ _ s)=> x ? /(itr_ext r1) ?; by exists x.
  case=> s6 /IH[s4 *]; exists s4=> //; apply/(itr_cons r1); by exists s6.
Qed.

End Commutation.

Arguments dcomm_scomm {_ _ _}.
Arguments dcomm_comm {_ _ _}.


Section Confluence.

Context {S : Type} (r : hrel S S).

Definition diamond_confluent := forall s1 s2 s3,
  r s1 s2 -> r s1 s3 -> exists2 s4, r s2 s4 & r s3 s4.

Definition confluent := forall s1 s2 s3,
  r^+ s1 s2 -> r^+ s1 s3 -> exists2 s4, r^+ s2 s4 & r^+ s3 s4.

Lemma dconfl_confl : diamond_confluent -> confluent.
Proof. exact/dcomm_comm. Qed.

End Confluence.

Arguments dconfl_confl {_ _}.

Section EqvRewriting.

Context {S : Type} (r e : hrel S S).

Hypothesis eqv_trans : Transitive e.
Hypothesis eqv_symm  : Symmetric e.
Hypothesis eqv_refl  : 1 \<= e.

Definition eqv_diamond_confluent := forall s1 s2 s3,
  r s1 s2 -> r s1 s3 ->
  exists s4 s4', [/\ r s2 s4, r s3 s4' & e s4 s4'].

Definition eqv_confluent := forall s1 s2 s3,
  r^+ s1 s2 -> r^+ s1 s3 ->
  exists s4 s4', [/\ r^+ s2 s4, r^+ s3 s4' & e s4 s4'].

Hypothesis edconfl : eqv_diamond_confluent.
Hypothesis edcomm : diamond_commute e r.

Lemma dcomm_rw_rw_eqv : diamond_commute r (r ⋅ e).
Proof.
  move=> s1 s2 s3 /= /edconfl D [s3' {D}/D[s4'' [s4' [? R ? /edcomm]]]].
  case/(_ _ R)=> x ??; exists x=> //; exists s4''=> //; exact/(eqv_trans _ s4').
Qed.

Lemma scomm_rw_eqv : strong_commute e r.
Proof.
  move=> s1 s2 s3 /[swap].
  have: e^+ \== e.
  - apply/(antisym _ _ _ (itr_ext e))/itr_ind_l1=> // [??[?]]; exact/eqv_trans.
  move=> E /(dcomm_comm edcomm) H /E /H [x ??]; exists x=> //; exact/E.
Qed.

Lemma rw_eqv_itr : (r ⋅ e)^+ \== r^+ ⋅ e.
Proof.
  apply/(antisym (r ⋅ e)^+ )=> [|s1 s2 [x ]].
  apply/itr_ind_l1=> [|s1 s3 [s2 [x + /eqv_symm R [y /scomm_rw_eqv-/(_ _ R)]]]].
  - exact/(dot_leq (itr_ext r) (leq_Reflexive e)).
  move=> s [s5 ? /eqv_symm/eqv_trans t/t ?]; exists s5=> //.
  apply/(itr_cons r); by exists x.
  suff: (r^+ \<= (fun s1 x => e x s2 -> (r ⋅ e)^+  s1 s2)).
  - exact.
  apply/itr_ind_l1=> {s1 x} [s1 x ?? |s1 x /= [y ? /[apply] ?]].
  - apply/(itr_ext (r ⋅ e)); by exists x.
  apply/(itr_cons (r ⋅ e)); do ? exists y=> //; exact/eqv_refl.
Qed.

Theorem confl_eqv : eqv_confluent.
Proof.
  move=> s1 s2 s3.
  move/(dcomm_comm dcomm_rw_rw_eqv) => /[swap]/[dup] _ rs.
  have: (r^+ ⋅ e) s1 s3.
  - by exists s3=> //; apply/eqv_refl.
  move/rw_eqv_itr=> R /(_ _ R)[x].
  by case/rw_eqv_itr=> y; exists y, x.
Qed.

End EqvRewriting.

Section EqvRRewriting.

Context {S : Type} (r e : hrel S S).

Hypothesis eqv_trans : Transitive e.
Hypothesis eqv_symm  : Symmetric e.
Hypothesis eqv_refl  : 1 \<= e.

Definition eqv_rdiamond_confluent := forall s1 s2 s3,
  r s1 s2 -> r s1 s3 ->
  exists s4 s4', [/\ r^? s2 s4, r^? s3 s4' & e s4 s4'].

Definition eqv_rconfluent := forall s1 s2 s3,
  r^* s1 s2 -> r^* s1 s3 ->
  exists s4 s4', [/\ r^* s2 s4, r^* s3 s4' & e s4 s4'].

Hypothesis edconfl : eqv_rdiamond_confluent.
Hypothesis edcomm : diamond_commute e r.

Theorem rconfl_eqv : eqv_rconfluent.
Proof.
  suff: eqv_confluent (r^?) e.
  - move=> C ???; rewrite !(str_itr r _ _) !(itr_qmk r _ _).
    move=>/C/[apply][[s4 [s4' [*]]]]; exists s4, s4'.
    by split=> //; rewrite !(str_itr r _ _) !(itr_qmk r _ _).
  apply/confl_eqv=> //.
  - move=> s1 s2 s3 [-> [->| ?]|R [<-|/(edconfl _ _ _ R)]] //.
    - exists s3, s3; split; by [left|left|apply/eqv_refl].
    - exists s3, s3; split; by [right|left|apply/eqv_refl].
    exists s2, s2; split; by [left|right|apply/eqv_refl].
  move=> ? s2 ? E [<-|/edcomm-/(_ _ E)[s4 *]].
  - exists s2=> //; by left.
  exists s4=> //; by right.
Qed.


End EqvRRewriting.

Definition exlab {T L : Type} (r : L -> hrel T T) : hrel T T :=
  fun t1 t2 => exists l, r l t1 t2.


Section EqvLabRewriting.

Context {S L : Type} (r : L -> hrel S S) (e : hrel S S).

Hypothesis eqv_trans : Transitive e.
Hypothesis eqv_symm  : Symmetric e.
Hypothesis eqv_refl  : 1 \<= e.

Definition eqv_diamond_commute (r r2 e : hrel S S) := forall s1 s2 s3,
   r s1 s2 -> r2 s1 s3 ->
   exists s4 s4', [/\ r2 s2 s4, r s3 s4' & e s4 s4'].

Definition eqv_rdiamond_commute (r r2 e : hrel S S) := forall s1 s2 s3,
   r s1 s2 -> r2 s1 s3 ->
   exists s4 s4', [/\ r2^? s2 s4, r^? s3 s4' & e s4 s4'].


Hypothesis ledrr : forall l1 l2, (eqv_rdiamond_commute (r l1) (r l2) e).
Hypothesis leder  : diamond_commute e (exlab r).

Lemma rexlab : exlab (fun l => (r l)^?) \<= (exlab r)^?.
Proof. move=> ?? /= [l [->|]]; [left|right] =>//; by exists l. Qed.


Theorem eqv_comm_union : eqv_rconfluent (exlab r) e.
Proof.
  apply/rconfl_eqv => // ???[l1 /ledrr C [l2 /C [s4 [s4' [*]]]]].
  - exists s4, s4'; do ? split=> //; apply/rexlab; by [exists l2| exists l1].
Qed.

End EqvLabRewriting.

Section EqRewritng.

Context {S : Type}.

Global Instance dcomm_weq: Proper
  ((weq : relation (hrel S S)) ==> (weq : relation (hrel S S))  ==> iff)
  diamond_commute.
Proof.
  move=> r1 r2 e12 r3 r4 e34; split=> D x y z /e12 + /e34;
    by move=> /D/[apply] [[z']] /e34 ? /e12 ?; exists z'.
Qed.

Global Instance eq_rconfl_weq: Proper
  ((weq : relation (hrel S S)) ==> (weq : relation (hrel S S))  ==> iff)
  eqv_rconfluent.
Proof.
  move=> r1 r2 e12 r3 r4 e34; split=> C x y z;
    move=> /(str_weq e12) + /(str_weq e12);
    move=> /C/[apply] [[y' [z' []]]] ?? /e34 ?;
    exists y', z'; split=> //; exact/(str_weq e12).
Qed.

End EqRewritng.

Section SubRewriting.

Local Open Scope ra_terms.

Context {S: eqType} {L : Type}.

(* rst --- restriction of a relation to a subset *)
Definition rst (p : rel.dset S) (r : hrel S S) : hrel S S :=
  r \& (p \x p).

(* TODO: develop a more general theory of `rst` which would subsume
 *   the following lemmas, and formulate it in terms of KA.
 *   In particular, the following lemmas might be useful.
 *   - rst p r \<= p × p
 *   - (rst p r)^+ \<= rst p r^+
 *   - p \<= p' -> r \<= r' -> rst p r \<= rst p' r' (a Proper lemma)
 *)

Lemma rst_p {p r x1 x2} : rst p r x1 x2 -> p x2.
Proof. by case=> ?/andP[]. Qed.

Lemma rst_itr_p {p r x1 x2} : (rst p r)^+ x1 x2 -> p x2.
Proof. by rewrite itr_str_r=> [[??/rst_p]]. Qed.

Lemma rst_str_p {p r x1 x2} : (rst p r)^* x1 x2 -> p x1 -> p x2.
Proof. by rewrite str_itr=> [[->|/rst_itr_p]]. Qed.

Context (p : rel.dset S) (r : L -> hrel S S) (e : hrel S S).

Implicit Types (s : S) (l : L).

Hypothesis eqv_trans : Transitive e.
Hypothesis eqv_symm  : Symmetric e.
Hypothesis eqv_refl  : 1 \<= e.

Hypothesis ledrr : forall l1 l2, eqv_rdiamond_commute (r l1) (r l2) e.
Hypothesis leder : diamond_commute e (exlab r).

Definition eqv_respect_p := [p] ⋅ e \<= e ⋅ [p].

Definition r_respect_p := forall l1 l2 s1 s2 s3 s,
  s2 != s3 ->
  rst p (r l1) s1 s2 ->
  rst p (r l2) s1 s3 ->
  r l2 s2 s -> p s.

Hypothesis eqv_p : eqv_respect_p.
Hypothesis eqv_r : r_respect_p.

Lemma r_exlab l: r l \<= exlab r.
Proof. by exists l. Qed.

Lemma rst_exlab : rst p (exlab r) \== exlab (rst p \o r).
Proof. by move=> ??; split=> [[[l]]|[l[]]] /=; last split=> //; exists l. Qed.

Lemma rsub l : rst p ((r l)^?) \<= ((rst p \o r) l)^? .
Proof. by move=> ?? [[-> ? | ??]]; [left | right]. Qed.

Lemma eqv_rr {l1 l2 s1 s2 s3 s}:
  s2 != s3 ->
  rst p (r l1) s1 s2 ->
  rst p (r l2) s1 s3 ->
  (r l2)^? s2 s -> p s.
Proof. by move=> N /[dup][[? /andP[?? /eqv_r/[apply] H [<-|/(H _ N)]]]]. Qed.

Theorem sub_eqv_comm_union : eqv_rconfluent (rst p (exlab r)) e.
Proof.
  rewrite rst_exlab.
  apply/eqv_comm_union=> //.
  - move=> l1 l2 ? s2 s3; case: (boolP (s2 == s3))=> [/eqP->|N].
    - exists s3, s3; split; [| |exact/eqv_refl]; by left.
   move=> /[dup] /(eqv_rr N) R[/ledrr] E /andP[??] /[dup]/R P[/E[s4 [x]]].
    case=> /[dup] /P ps4 ?? /[dup] ?.
    have/eqv_p[??[->??/andP[??]]]: ([p] ⋅ e) s4 x by exists s4.
    exists s4, x; do ? split=> //; apply/rsub; split=> //; exact/andP.
  move=> s1 s2 s /= /[dup] ? /leder E [? [/r_exlab /E [x [l ?? /andP[??]]]]].
  have/eqv_p[??[->?]]: ([p] ⋅ e) s  x  by exists s.
  have/eqv_p[??[->?]]: ([p] ⋅ e) s1 s2 by exists s1.
  exists x=> //; exists l; split=> //; exact/andP.
Qed.

End SubRewriting.

Section SubTypeRewriting.

Context {S : eqType} {L T : Type} (f : T -> S).

Definition relpreim r : hrel T T :=
  fun x y => r (f x) (f y).

Context (p : rel.dset S) (r : hrel S S) (e : hrel S S) .

Hypothesis im    : forall x, p x -> exists y, f y = x.
Hypothesis p_f   : forall x, p (f x).
Hypothesis f_inj : injective f.
Hypothesis confl : eqv_rconfluent (rst p r) e.

Lemma relpreim_itr: (relpreim (rst p r))^* \== relpreim (rst p r)^*.
Proof.
  apply/(antisym ((relpreim (rst p r))^*)); rewrite /relpreim.
  - apply/str_ind_l1=> [??->|??]; first exact/(str_refl (rst p r)).
    by case=> x ??; apply/(str_cons (rst p r)); exists (f x).
  move=> a b H. move: {-2}(f b) {-2}(f a) H (erefl (f a)) (erefl (f b))=> f1 f2.
  move: a=> /[swap].
  suff: (rst p r)^* \<=
  (fun f2 f1 => forall a, f a = f2 -> f b = f1 -> ((relpreim (rst p r))^* a b)).
  - exact.
  apply/str_ind_l1=> [??-> ? <- /f_inj->|??[? /[dup]]].
  - exact/(str_refl (relpreim(rst p r))).
  move/(@rst_p _ p); case/im=> x <- ? /(_ _ erefl) H ? E /H ?.
  apply/(str_cons (relpreim (rst p r))).
  by exists x=> //; rewrite /relpreim E.
Qed.

Arguments p_f {_}.

Lemma confl_sub : eqv_rconfluent (relpreim r) (relpreim e).
Proof.
  have->: relpreim r \== relpreim (rst p r).
  - by move=> ?? /=; rewrite /rst /relpreim /= ?p_f; split=> // [[]].
  move=> ??? /=.
  rewrite ?(relpreim_itr _ _) /relpreim=> /confl/[apply].
  case=> ? [?[/[dup] /(rst_str_p)/(_ p_f)/im[s4 <- ?]]].
  move/[dup]/(rst_str_p)/(_ p_f)/im=>[s4'<- ?].
  exists s4, s4'; split=> //=; by rewrite relpreim_itr.
Qed.

End SubTypeRewriting.

Section Terminal.

Context {S : Type} (r e : hrel S S).

Hypothesis confl : eqv_rconfluent r e.
Hypothesis edcomm : diamond_commute e r.

Hypothesis eqv_trans : Transitive e.
Hypothesis eqv_symm  : Symmetric e.
Hypothesis eqv_refl  : 1 \<= e.

Hypothesis e_r     : e \& r^+ \<= bot.

(* We use categorical meaning of initial/terminal element *)
Definition initial s0 := forall s, r^* s0 s.
Definition terminal st := forall s, (r^* ⋅ e) s st.

Context s0 (init : initial s0).

Lemma terminal_max : maximal r \== terminal.
Proof.
  rewrite maximal_str=> st; split=> [/[swap] s M|/[swap] s /(_ s) /[swap]].
  - case: (confl _ _ _ (init st) (init s))=> s' [s'' [/M-> ??]].
    by exists s''=> //; exact/eqv_symm.
  rewrite {1}str_itr=> [[]] // /[swap][[s']].
  rewrite str_itr=> [[-> |?]] /eqv_symm*; exfalso; first exact/(e_r st s').
  apply/(e_r st s'); split=> //; apply/(itr_trans r); by exists s.
Qed.

End Terminal.
