From RelationAlgebra Require Import lattice monoid rel kat_tac kleene.
From mathcomp Require Import ssreflect ssrbool ssrfun.
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
(*   commutative_diamond_prop (~>) (>>) == ∀ s1 s2 s3                        *)
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
(*   diamond_prop (~>)                   == commuting_diamond_prop (~>) (~>) *)
(*   confluence   (~>)                   == commute (~>) (~>)                *)
(*   commutation_lemma                   <-> commuting_diamond_prop (~>) (>>)*)
(*                                       implies commute (~>) (>>)           *)
(*   Newman                              <-> diamond_prop (~>) implies       *)
(*                                       confluence (~>)                     *)
(* In the ERewritingSystem we have the general theory of the rewriting system*)
(* with some equivalence relation. It is more comfortible to derive a such   *)
(* theory using lemmas about casual rewriting system with two rewriting rules*)
(*   s1 ~>   s2              ==  the rewriting rule                          *)
(*   s1 ~~   s2              ==  the equivalence relation                    *)
(*   s2 ~>~  s2              ==   ~> ⋅ ~~                                    *)
(*   s1 ~>+~ s2              ==  ~>⁺ ⋅ ~~                                    *)
(*   s1 ~>~+ s2              ==  (~> ⋅ ~~)⁺                                  *)
(*   ediamond_prop (~>) (~~) == version of the diamond property for the      *)
(*                         rewriting systems with equivalence: it states that*)
(*                         s1 ~> s2 and s1 ~> s3 implies existance of some s4*)
(*                         and s4' s.t. s2 ~> s4, s3 ~> s4' and s4 ~~ s4'.   *)
(*   econfluence (~>) (~~)   == the confluence principle for the rewriting   *)
(*                         systems with an equivalence relation:             *)
(*             s1 ~>⁺ s2 |                                                   *)
(*                       | ==> exists s4 ~~ s4' s.t. s2 ~>⁺ s4 and s3 ~>⁺ s4'*)
(*             s1 ~>⁺ s3 |                                                   *)
(*   ENewman               <-> commuting_diamond_prop (~>) (~~) with         *)
(*                      ediamond_prop (~>) (~~) implies econfluence (~>) (~~)*)
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
  exists s4 s4', (r s2 s4 * r s3 s4 * e s4 s4')%type.

Definition eqv_confluent := forall s1 s2 s3,
  r^+ s1 s2 -> r^+ s1 s3 -> 
  exists s4 s4', (r^+ s2 s4 * r^+ s3 s4' * e s4 s4')%type.

Hypothesis edconfl : eqv_diamond_confluent.
Hypothesis edcomm : diamond_commute e r.

Lemma dcomm_rw_rw_eqv : diamond_commute r (r ⋅ e).
Proof.
  move=> s1 s2 s3 /= /edconfl D [s3' {D}/D[s4'' [s4' [[? R ? /edcomm]]]]].
  case/(_ _ R)=> x ??; exists x=> //; exists s4''=> //; exact/(eqv_trans _ s4').
Qed.

Lemma scomm_rw_eqv : strong_commute e r.
Proof.
  move=> s1 s2 s3 /[swap].
  have: e^+ ≡ e.
  - by apply/(antisym _ _ _ (itr_ext e))/itr_ind_l1=> // ++ [/[swap]]. 
  move=> E /(dcomm_comm edcomm) H /E /H [x +]; exists x=> //; exact/E. 
Qed.

Lemma rw_eqv_itr : (r ⋅ e)^+ ≡ r^+ ⋅ e.
Proof.
  apply/(antisym (r ⋅ e)^+ )=> [|s1 s2 [x ]].
  apply/itr_ind_l1=> [|s1 s3 [s2 [x + /eqv_symm R [y /scomm_rw_eqv-/(_ _ R)]]]]. 
  - exact/(dot_leq (itr_ext r) (leq_Reflexive e)).
  move=> s [s5 ? /eqv_symm/eqv_trans t/t ?]; exists s5=> //. 
  apply/(itr_cons r); by exists x.
  suff: (r^+ ≦ (fun s1 x => e x s2 -> (r ⋅ e)^+  s1 s2)).
  - apply.
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
