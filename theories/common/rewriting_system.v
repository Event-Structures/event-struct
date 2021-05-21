From RelationAlgebra Require Import lattice monoid rel kat_tac kat kleene.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice.
From eventstruct Require Import utils relalg.

(*****************************************************************************)
(* exlaberal theory of rewriting systems                                       *)
(* inspired by "Term Rewriting and All That"                                 *)
(* Fisrt section called Commutation. Here the theory of exlaberal rewriting    *)
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
(*                              ⋮     ⋮                                      *)
(*                              v     v                                      *)
(*                              v     v                                      *)
(*                              s3 ~> s4 - exists                            *)
(*   commute (~>) (>>)                  == ∀ s1 s2 s3                        *)
(*                              s1 ~>  ...  ~> s2                            *)
(*                              v              v                             *)
(*                              v              v                             *)
(*                              ⋮              ⋮                             *)
(*                              v              v                             *)
(*                              v              v                             *)
(*                              s3 ~>  ...  ~> s4 - exists                   *)
(*   diamond_confluent (~>)              == diamond_commute (~>) (~>)        *)
(*   confluence   (~>)                   == commute (~>) (~>)                *)
(*   dcomm_comm                          <-> commuting_diamond_prop (~>) (>>)*)
(*                                       implies commute (~>) (>>)           *)
(*   dconfl_confl                        <-> diamond_confluent (~>) implies  *)
(*                                       confluence (~>)                     *)
(* In the EqvRewriting we have the exlaberal theory of the rewriting system    *)
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
(* But want to exlaberalize this lemma in two steps:                           *)
(*   1) let us have an arbitrary number of relations -- we model it by       *)
(*      consindering one labeling relation: r : L -> hrel S S, where L is an *)
(*      arbitrary label Type                                                 *)
(*   2) let us parametrize this lemma with some equivalence relation         *)
(* Let L and S be some types and r : L -> hrel S S                           *)
(* eqv_diamond_commute (~>) (>>) (~~) == version of the diamond property for *)
(*                         the rewriting systems with equivalence: it states *)
(*                         that s1 ~> s2 and s1 ~> s3 implies existance of   *)
(*                         some s4 and s4' s.t. s2 ~> s4, s3 ~> s4' and      *)
(*                         that s1 ~> s2 and s1 >> s3 implies existance of   *)
(*                         some s4 and s4' s.t. s2 ~> s4, s3 >> s4' and      *)
(*                        exlab r s1 s2 == ∃ l, s.t. r l s1 s2 holds           *)
(*            eqv_diamoind_commute r e <-> if forall two labels l₁ l₂ we now *)
(*                         that eqv_diamond_commute (r l1) (r l2) (~~) and   *)
(*                         diamond_commute (exlab r) (~~) than exlab r is        *)
(*                         conluent w.r.t (~~) i.e eqv_confluent (exlab r) (~~)*)
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
(*                        eqv_confluent (exlab (sub ∘ r)) (sub ~~)             *)
(*****************************************************************************)

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
  suff: (r2^+ ≦ (fun s1 s3 => forall s2 : S, r1 s1 s2 -> exists2 s4 : S, r2^+ s2 s4 & r1 s3 s4)).
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
  suff: (r1^+ ≦ (fun s1 s2 => forall s3, r2^+ s1 s3 -> exists2 s4, r2^+ s2 s4 & r1^+ s3 s4)).
  - exact.
  apply/itr_ind_l1=> {s1 s2} [?? s?|s1 s2 /= [s5 /(dcomm_scomm d) c IH s3 /c]].
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
Hypothesis eqv_refl  : 1 ≦ e.

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
  have: e^+ ≡ e.
  - apply/(antisym _ _ _ (itr_ext e))/itr_ind_l1=> // [??[?]]; exact/eqv_trans.
  move=> E /(dcomm_comm edcomm) H /E /H [x ??]; exists x=> //; exact/E. 
Qed.

Lemma rw_eqv_itr : (r ⋅ e)^+ ≡ r^+ ⋅ e.
Proof.
  apply/(antisym (r ⋅ e)^+ )=> [|s1 s2 [x ]].
  apply/itr_ind_l1=> [|s1 s3 [s2 [x + /eqv_symm R [y /scomm_rw_eqv-/(_ _ R)]]]]. 
  - exact/(dot_leq (itr_ext r) (leq_Reflexive e)).
  move=> s [s5 ? /eqv_symm/eqv_trans t/t ?]; exists s5=> //. 
  apply/(itr_cons r); by exists x.
  suff: (r^+ ≦ (fun s1 x => e x s2 -> (r ⋅ e)^+  s1 s2)).
  - exact.
  apply/itr_ind_l1=> {s1 x} [s1 x ??|s1 x /= [y ? /[apply] ?]].
  - apply/(itr_ext (r ⋅ e)); by exists x.
  apply/(itr_cons (r ⋅ e)); do ? exists y=> //; exact/eqv_refl.
Qed.

Theorem confl_eqv : eqv_confluent.
Proof.
  move=> s1 s2 s3.
  move/(dcomm_comm dcomm_rw_rw_eqv) => /[swap]/[dup] ? /[-! dotx1 r^+ s1].
  move/(dot_leq (leq_Reflexive r^+) eqv_refl) /rw_eqv_itr=> R /(_ _ R)[x].
  by case/rw_eqv_itr=> y; exists y, x.
Qed.

End EqvRewriting. 

Definition exlab {T L : Type} (r : L -> hrel T T) : hrel T T := 
  fun t1 t2 => exists l, r l t1 t2.


Section EqvLabRewriting.

Context {S L : Type} (r : L -> hrel S S) (e : hrel S S).

Hypothesis eqv_trans : Transitive e.
Hypothesis eqv_symm  : Symmetric e.
Hypothesis eqv_refl  : 1 ≦ e.

Definition eqv_diamond_commute (r1 r2 e : hrel S S) := forall s1 s2 s3, 
   r1 s1 s2 -> r2 s1 s3 -> 
   exists s4 s4', [/\ r2 s2 s4, r1 s3 s4' & e s4 s4'].


Hypothesis ledrr : forall l1 l2, (eqv_diamond_commute (r l1) (r l2) e).
Hypothesis leder  : diamond_commute e (exlab r).

Theorem eqv_comm_union : eqv_confluent (exlab r) e.
Proof.
  apply/confl_eqv => // ???[l1 /ledrr C [l2 /C [s4 [s4' [*]]]]].
  - exists s4, s4'; do ? split=> //; by [exists l2| exists l1].
Qed.

End EqvLabRewriting.

Section EqRewritng.

Context {S : Type} (r1 r1' r2 r2' e e' : hrel S S).

Global Instance dcomm_weq: Proper 
  ((weq : relation (hrel S S)) ==> (weq : relation (hrel S S))  ==> iff) 
  diamond_commute.
Proof.
  move=> ?? E1 ?? E2; split=> D ???.
  - rewrite -(E1 _ _) -(E2 _ _)=> /D/[apply][[s]].
    rewrite (E1 _ _) (E2 _ _); by exists s.
  rewrite (E1 _ _) (E2 _ _)=> /D/[apply][[s]].
  rewrite -(E1 _ _) -(E2 _ _); by exists s.
Qed.

Global Instance eq_confl_weq: Proper
  ((weq : relation (hrel S S)) ==> (weq : relation (hrel S S))  ==> iff) 
  eqv_confluent.
Proof.
  move=> ?? E ?? E'; split=> D ???.
  - rewrite -?(kleene.itr_weq E _ _)=> /D/[apply][[s1 [s2]]].
    rewrite ?(kleene.itr_weq E _ _) (E' _ _); by exists s1, s2.
  rewrite ?(kleene.itr_weq E _ _)=> /D/[apply][[s1 [s2]]].
  rewrite -?(kleene.itr_weq E _ _) -(E' _ _); by exists s1, s2.
Qed.

End EqRewritng.

Section SubRewriting.

Local Open Scope ra_terms.

Context {S L : Type} (p : rel.dset S).

Definition sub (r : hrel S S) : hrel S S := r ⊓ (p × p).

Lemma sub_p {r x1 x2} : sub r x1 x2 -> p x2.
Proof. by case=> ?/andP[]. Qed.

Lemma sub_itr_p {r x1 x2} : (sub r)^+ x1 x2 -> p x2.
Proof. by rewrite itr_str_r=> [[??/sub_p]]. Qed.

Context (r : L -> hrel S S) (e : hrel S S).

Implicit Types (s : S) (l : L).

Hypothesis eqv_trans : Transitive e.
Hypothesis eqv_symm  : Symmetric e.
Hypothesis eqv_refl  : 1 ≦ e.

Hypothesis ledrr : forall l1 l2, eqv_diamond_commute (r l1) (r l2) e.
Hypothesis leder : diamond_commute e (exlab r).

Definition eqv_respect_p := [p] ⋅ e ≦ e ⋅ [p].

Definition r_respect_p := forall l1 l2 s1 s2 s3 s,
  sub (r l1) s1 s2 -> 
  sub (r l2) s1 s3 ->
  r l2 s2 s -> p s.

Hypothesis eqv_p : eqv_respect_p.
Hypothesis eqv_r : r_respect_p.

Lemma r_exlab l: r l ≦ exlab r.
Proof. by exists l. Qed.

Lemma sub_exlab : sub (exlab r) ≡ exlab (sub \o r).
Proof. by move=> ??; split=> [[[l]]|[l[]]] /=; last split=> //; exists l. Qed.

Theorem sub_eqv_comm_union : eqv_confluent (sub (exlab r)) e.
Proof.
  rewrite sub_exlab.
  apply/eqv_comm_union=> //.
  - move=> ????? /= /[dup] /eqv_r R[/ledrr] E /andP[??] /[dup]/R P[/E[s4 [x]]].
    case=> /[dup] /P ps4 ?? /[dup] ?.
    have/eqv_p[??[->??/andP[??]]]: ([p] ⋅ e) s4 x by exists s4.
    exists s4, x; do ? split=> //; exact/andP.
  move=> s1 s2 s /= /[dup] ? /leder E [? [/r_exlab /E [x [l ?? /andP[??]]]]].
  have/eqv_p[??[->?]]: ([p] ⋅ e) s  x  by exists s.
  have/eqv_p[??[->?]]: ([p] ⋅ e) s1 s2 by exists s1.
  exists x=> //; exists l; split=> //; exact/andP.
Qed.

End SubRewriting.

Section SubTypeRewriting.

Context {L : Type}.

Context {S : Type} (r1 : hrel S S) (e1 : hrel S S) (p : rel.dset S).

Context {T : Type} (r2 : hrel T T) (e2 : hrel T T) (f : T -> S).

Definition relpreim r : hrel T T :=
  fun x y => r (f x) (f y).

Hypothesis (morph_f_e1 : e2 ≡ relpreim e1).
Hypothesis (morph_f_r1 : r2 ≡ relpreim (sub p r1)).
Hypothesis (im : forall x, p x -> exists y, f y = x).

Hypothesis (confl : eqv_confluent (sub p r1) e1).

Lemma relpreim_itr: (relpreim (sub p r1))^+ ≡ relpreim (sub p r1)^+.
Proof.
  apply/(antisym ((relpreim (sub p r1))^+)); rewrite /relpreim.
  - apply/itr_ind_l1; move=> ??; first exact/(itr_ext (sub p r1)).
    by case=> x ??; apply/(itr_cons (sub p r1)); exists (f x).
  move=> a b H. move: {-2}(f b) {-2}(f a) H (erefl (f a)) (erefl (f b))=> f1 f2.
  move: a=> /[swap].
  suff: (sub p r1)^+ ≦ 
  (fun f2 f1 => forall a, f a = f2 -> f b = f1 -> ((relpreim (sub p r1))^+ a b)).
  - exact.
  apply/itr_ind_l1=> [??/[swap]?/[swap]<-/[swap]<-|??[? /[dup]/(sub_p _)]].
  - exact/(itr_ext (relpreim(sub p r1))).
  case/im=> x <- ? /(_ _ erefl) H ? E /H ?; apply/(itr_cons (relpreim (sub p r1))).
  by exists x=> //; rewrite /relpreim E.
Qed.

Lemma confl_sub : eqv_confluent r2 e2.
Proof.
  rewrite morph_f_e1 morph_f_r1 => ??? /=.
  rewrite ?(relpreim_itr _ _) /relpreim=> /confl/[apply].
  case=> ? [?[/[dup]]] /(sub_itr_p _)/im[s4<- ?].
  move/[dup]/(sub_itr_p _)/im=>[s4'<- ?].
  exists s4, s4'; split=> //=; by rewrite relpreim_itr.
Qed.

End SubTypeRewriting.


