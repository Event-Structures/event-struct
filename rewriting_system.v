From RelationAlgebra Require Import lattice monoid rel kat_tac kleene.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice.
From event_struct Require Import utilities.

(*****************************************************************************)
(* General theory of rewriting systems                                       *)
(* Fisrt section called RewritingSystem. Here the theory of general rewriting*)
(* systems with to rewriting rules derived:                                  *)
(*   s1 ~>  s2                ==  the first rewriting rule                   *)
(*   s2 ~>+ s2                ==  transitive closure of the first rule       *)
(*   s2 >>  s2                ==  the second rewriting rule                  *)
(*   s2 >>+ s2                ==  transitive closure of the second rule      *)
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
(* In the ERewritingSystem we have the general theory of the rewriting system*)
(* with some equivalence relation. It is more comfortible to derive a such   *)
(* theory using lemmas about casual rewriting system with two rewriting rules*)
(*   s1 ~>   s2              ==  the rewriting rule                          *)
(*   s1 ~~   s2              ==  the equivalence relation                    *)
(*   s2 ~>~  s2              ==   ~> ⋅ ~~                                    *)
(*   s1 ~>+~ s2              ==  ~>⁺ ⋅ ~~                                    *)
(*   s1 ~>~+ s2              ==  (~> ⋅ ~~)⁺                                  *)
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
(*                         eqv_confluent (~>) (~~)                            *)
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


Section EqvCommtation.

Context {S : Type} (r1 r2 e : hrel S S).

Hypothesis eqv_trans : Transitive e.
Hypothesis eqv_symm  : Symmetric e.
Hypothesis eqv_refl  : 1 ≦ e.

Definition eqv_diamond_commute := forall s1 s2 s3, 
  r1 s1 s2 -> r2 s1 s3 -> 
  exists s4 s4', (r2 s2 s4 * r1 s3 s4' * e s4 s4')%type.

Definition eqv_commute := forall s1 s2 s3,
  r1^+ s1 s2 -> r2^+ s1 s3 -> 
  exists s4 s4', (r2^+ s2 s4 * r1^+ s3 s4' * e s4 s4')%type.

Hypothesis edconfl : eqv_diamond_commute.
Hypothesis edcomm1 : diamond_commute e r1.
Hypothesis edcomm2 : diamond_commute e r2.

Lemma dcomm_rw_rw_eqv : diamond_commute r2 (r1 ⋅ e).
Proof.
  move=> s1 s2 s3 /= /edconfl D [s3' {D}/D [s4'' [s4' [[R ?? /edcomm2]]]]].
  case/(_ _ R)=> x ??; exists x=> //; exists s4'=> //.
  apply/(eqv_trans _ s4'')=> //; exact/eqv_symm.
Qed.

Lemma scomm_rw_eqv : strong_commute e r1.
Proof.
  move=> s1 s2 s3 /[swap].
  have: e^+ ≡ e.
  - apply/(antisym _ _ _ (itr_ext e))/itr_ind_l1=> // [??[?]]; exact/eqv_trans.
  move=> E /(dcomm_comm edcomm1) H /E /H [x ??]; exists x=> //; exact/E. 
Qed.

Lemma rw_eqv_itr : (r1 ⋅ e)^+ ≡ r1^+ ⋅ e.
Proof.
  apply/(antisym (r1 ⋅ e)^+ )=> [|s1 s2 [x ]].
  apply/itr_ind_l1=> [|s1 s3 [s2 [x + /eqv_symm R [y /scomm_rw_eqv-/(_ _ R)]]]]. 
  - exact/(dot_leq (itr_ext r1) (leq_Reflexive e)).
  move=> s [s5 ? /eqv_symm/eqv_trans t/t ?]; exists s5=> //. 
  apply/(itr_cons r1); by exists x.
  suff: (r1^+ ≦ (fun s1 x => e x s2 -> (r1 ⋅ e)^+  s1 s2)).
  - exact.
  apply/itr_ind_l1=> {s1 x} [s1 x ??|s1 x /= [y ? /[apply] ?]].
  - apply/(itr_ext (r1 ⋅ e)); by exists x.
  apply/(itr_cons (r1 ⋅ e)); do ? exists y=> //; exact/eqv_refl.
Qed.

Theorem comm_eqv : eqv_commute.
Proof.
  move=> s1 s2 s3 /[swap].
  move/(dcomm_comm dcomm_rw_rw_eqv) => /[swap]/[dup] ? /[-! dotx1 r1^+ s1].
  move/(dot_leq (leq_Reflexive r1^+) eqv_refl) /rw_eqv_itr=> R /(_ _ R)[x].
  case/rw_eqv_itr=> y; exists x, y; do? split=> //; exact/eqv_symm.
Qed.

End EqvCommtation.

Section EqvConfulence.

Context {S : Type} (r e : hrel S S).

Hypothesis eqv_trans : Transitive e.
Hypothesis eqv_symm  : Symmetric e.
Hypothesis eqv_refl  : 1 ≦ e.

Definition eqv_diamond_confluent := 
  eqv_diamond_commute r r e.

Definition eqv_confluent := 
  eqv_commute r r e.

Hypothesis edconfl : eqv_diamond_confluent.
Hypothesis edcomm : diamond_commute e r.

Theorem eqv_confl : eqv_confluent.
Proof.
  exact/(comm_eqv _ _ _ eqv_trans eqv_symm eqv_refl edconfl edcomm edcomm).
Qed.


End EqvConfulence.

Definition gen {T L : Type} (r : L -> hrel T T) : hrel T T := 
  fun t1 t2 => exists l, r l t1 t2.


Section ELabRewritingSystem.

Context {S L : Type} (r : L -> hrel S S) (e : hrel S S).

Hypothesis eqv_trans : Transitive e.
Hypothesis eqv_symm  : Symmetric e.
Hypothesis eqv_refl  : 1 ≦ e.

Hypothesis ledrr : forall l1 l2, (eqv_diamond_commute (r l1) (r l2) e).
Hypothesis leder  : forall l, diamond_commute e (r l).

Theorem eqv_comm_union : eqv_confluent (gen r) e.
Proof.
  apply/eqv_confl=> // [???[l1 /ledrr C [l2 /C [s4 [s4' [[*]]]]]]|???/leder C].
  - exists s4, s4'; do ? split=> //; by [exists l2| exists l1].
  case=> l /C[s4 *]; exists s4=> //; by exists l.
Qed.

End ELabRewritingSystem.

Section SubRewritingSystem.

Context {S : eqType} {L : Type} {p : pred S} {T : subType p}.

Definition sub (r : hrel S S) : hrel T T :=
  fun t1 t2 => r (val t1) (val t2).

Context (r : L -> hrel S S) (e : hrel S S).

Implicit Types (t : T) (s : S) (l : L).

Hypothesis eqv_trans : Transitive e.
Hypothesis eqv_symm  : Symmetric e.
Hypothesis eqv_refl  : 1 ≦ e.

Hypothesis ledrr : forall l1 l2, (eqv_diamond_commute (r l1) (r l2) e).
Hypothesis leder  : forall l, diamond_commute e (r l).

Definition eqv_respect_p := forall s (t : T), e (val t) s -> p s.

Definition r_respect_p := forall l1 l2 t1 t2 t3 s,
  sub (r l1) t1 t2 -> 
  sub (r l2) t1 t3 ->
  r l2 (val t2) s -> p s.

Hypothesis eqv_p : eqv_respect_p.
Hypothesis eqv_r : r_respect_p.

Theorem sub_eqv_comm_union : eqv_confluent (gen (sub \o r)) (sub e).
Proof.
  apply/eqv_comm_union.
  - rewrite /sub=>> /eqv_trans; exact.
  - rewrite /sub=>> /eqv_symm; exact.
  - rewrite /sub=> x1 x2 /=->; exact/eqv_refl.
  - move=> ????? /= /[dup] /eqv_r R /ledrr E /[dup] /R P /E[s4 [? [[/[dup]]]]].
    move=> /P ps4 ?? /[dup]; rewrite -{1}[s4](@SubK S p T)=> /eqv_p ps4' ?.
    by exists (Sub _ ps4), (Sub _ ps4'); do ? split; rewrite /sub ?SubK //.
  move=> ???? /= /leder /[apply][[?? /[dup] /eqv_p ps ?]].
  by exists (Sub _ ps); rewrite /sub SubK.
Qed.

End SubRewritingSystem.



