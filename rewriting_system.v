From RelationAlgebra Require Import lattice monoid rel kat_tac kleene.
From mathcomp Require Import ssreflect ssrbool ssrfun.
From event_struct Require Import utilities.

<<<<<<< HEAD
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
=======
(******************************************************************************)
(* General theory of rewriting systems                                        *)
(* Fisrt section called RewritingSystem. Here the theory of general rewriting *)
(* systems with to rewriing rules derived:                                    *)
(*   s1 ~>  s2                ==  the first rewriting rule                    *)
(*   s2 ~>+ s2                ==  transitive closure of the first rule        *)
(*   s2 >>  s2                ==  the second rewriting rule                   *)
(*   s2 >>+ s2                ==  transitive closure of the second rule       *)
(*   diamond_prop s1 s2 s3    ==  the dainomd property on s1 s2 and s3. It    *)
(*                            states that if one can rewrite s1 with the fist *)
(*                            rule to s2 (ie. s1 ~> s2) and with the second   *)
(*                            rule to s3 (ie. s1 >> s3) then exists some s4   *)
(*                            s.t. s2 >> s4 and s3 ~> s4:                     *)
(*                                                                            *)
(*                              s1 ~> s2                                      *)
(*                              v     v                                       *)
(*                              v     v                                       *)
(*                              s3 ~> s4 - exists                             *)
(*                                                                            *)
(*   half_confluence s1 s2 s3 == auxilary lemma about confluence              *)
(*   confluence s1 s2 s3      <-> the confluence theorem: it states that if   *)
(*                            the rewriting sysytem satisfies the dianomd     *)
(*                            property s1 ~>+ s2 and s2 >>+ s3 then exists s4 *)
(*                            s.t. s2 >>+ s4 and s3 ~>+ s4:                   *)
(*                                                                            *)
(*                              s1 ~>  ...  ~> s2                             *)
(*                              v              v                              *)
(*                              v              v                              *)
(*                              .              .                              *)
(*                              .              .                              *)
(*                              .              .                              *)
(*                              v              v                              *)
(*                              v              v                              *)
(*                              s3 ~>  ...  ~> s4 - exists                    *)
(* In the ERewritingSystem we have the general theory of the rewriting systems*)
(* with some equivalence relation. It is more comfortible to derive a such    *)
(* theory using lemmas about casual rewriting system with two rewriting rules *)
(*   s1 ~>   s2             ==  the rewriting rule                            *)
(*   s1 ~~   s2             ==  the equivalence relation                      *)
(*   s2 ~>~  s2             ==   ~> ⋅ ~~                                      *)
(*   s1 ~>+~ s2             ==  ~>⁺ ⋅ ~~                                      *)
(*   s1 ~>~+ s2             ==  (~> ⋅ ~~)⁺                                    *)
(*   ediamond_prop s1 s2 s3 <-> version of the diamond property for the       *)
(*                         rewriting systems with equivalence: it states that *)
(*                         s1 ~> s2 and s1 ~> s3 implies existance of some s4 *)
(*                         and s4' s.t. s2 ~> s4, s3 ~> s4' and s4 ~~ s4'.    *)
(*   equiv_prop s1 s2 s3   <-> if s1 ~> s2 and s1 ~~ s3 then there is some s4 *)
(*                         s.t. s3 ~> s4 and s2 ~~ s4                         *)
(*   econfluence s1 s2 s3  <-> the confluence principle for the rewriting     *)
(*                         systems with an equivalence relation:              *)
(*             s1 ~>⁺ s2 |                                                    *)
(*                       | ==> exists s4 ~~ s4' s.t. s2 ~>⁺ s4 and s3 ~>⁺ s4' *)
(*             s1 ~>⁺ s3 |                                                    *)
(******************************************************************************)

Section RewritingSystem.

Context {S : Type} (rw1 rw2 : hrel S S).

Notation "s1 ~> s2" := (rw1 s1 s2) (at level 20).
Notation "s1 >> s2" := (rw2 s1 s2) (at level 20).

Definition diamond_prop := forall s1 s2 s3, 
  s1 ~> s2 -> s1 >> s3 -> exists2 s4, s2 >> s4 & s3 ~> s4.

Hypothesis ((* shine on you crazy *) diamond : diamond_prop).

Notation "s1 ~>+ s2" := (rw1^+ s1 s2) (at level 20).
Notation "s1 >>+ s2" := (rw2^+ s1 s2) (at level 20).

Lemma half_confluence {s1 s2 s3}: 
  s1 ~> s2 -> s1 >>+ s3 -> exists2 s4 : S, s2 >>+ s4 & s3 ~> s4.
Proof.
  move=> + str; move: str s2.
  suff: (rw2^+ ≦ (fun s1 s3 => forall s2 : S, s1 ~> s2 -> exists2 s4 : S, s2 >>+ s4 & s3 ~> s4)).
  - apply.
  apply/itr_ind_l1=> {s1 s3} [?? /diamond d ? /d[x /(itr_ext rw2) *]|s1 s3 /=].
  - by exists x.
  move=> [? /diamond d IH ? /d[x ? /IH[y *]]]; exists y=> //.
  apply/(itr_cons rw2); by exists x.
Qed.

Lemma confluence s1 s2 s3: 
  s1 ~>+ s2 -> s1 >>+ s3 -> exists2 s4, s2 >>+ s4 & s3 ~>+ s4.
Proof.
  move: s3=> /[swap].
  suff: (rw1^+ ≦ (fun s1 s2 => forall s3, s1 >>+ s3 -> exists2 s4, s2 >>+ s4 & s3 ~>+ s4)).
  - apply.
  apply/itr_ind_l1=> {s1 s2} [?? s?|s1 s2 /= [s5 /half_confluence c IH s3 /c]].
  - case/(half_confluence s)=> x ? /(itr_ext rw1) ?; by exists x.
  case=> s6 /IH[s4 *]; exists s4=> //; apply/(itr_cons rw1); by exists s6.
Qed.

(* TODO: add lemma about maximal element *)

End RewritingSystem.

Arguments confluence {_ _ _}.

Section ERewritingSystem.

Variables (S : Type) (rw eqv : hrel S S).

Notation "s1 ~> s2"   := (rw           s1 s2) (at level 20).
Notation "s1 ~>+ s2"  := (rw^+         s1 s2) (at level 20).
Notation "s1 ~~ s2"   := (eqv          s1 s2) (at level 20).
Notation "s1 ~>~ s2"  := (rw ⋅ eqv     s1 s2) (at level 20).
Notation "s1 ~>+~ s2" := (rw^+ ⋅ eqv   s1 s2) (at level 20).
Notation "s1 ~>~+ s2" := ((rw ⋅ eqv)^+ s1 s2) (at level 20).

Definition ediamond_prop := forall s1 s2 s3, 
  s1 ~> s2 -> s1 ~> s3 -> 
  exists s4 s4', (s2 ~> s4 * s3 ~> s4' * s4 ~~ s4')%type.

Definition equiv_prop := forall s1 s2 s3, 
    s1 ~~ s2 -> s1 ~> s3 -> 
      exists2 s4 , s2 ~> s4 & s3 ~~ s4.

Hypothesis eqv_trans : forall e2 e1 e3, e1 ~~ e2 -> e2 ~~ e3 -> e1 ~~ e3.
Hypothesis eqv_symm  : forall e1 e2, e1 ~~ e2 -> e2 ~~ e1.
Hypothesis eqv_refl  : 1 ≦ eqv.
Hypothesis ediamond : ediamond_prop.
Hypothesis equiv : equiv_prop.

Lemma diamond_rwe : diamond_prop rw (rw ⋅ eqv).
Proof.
move=> s1 s2 s3 /= /ediamond d [s3' {d}/d[s4'' [s4' [[? e ? /equiv]]]]].
case/(_ _ e)=> x ??; exists x=> //; exists s4''=> //; exact/(eqv_trans s4').
Qed.

Lemma diamond_eqv s1 s2 s3 :
  s1 ~>+ s3 -> s1 ~~ s2 -> exists2 s4, s2 ~>+ s4 & s3 ~~ s4.
Proof.
  have: eqv^+ ≡ eqv.
  - by apply/(antisym _ _ _ (itr_ext eqv))/itr_ind_l1=> // ++ [/[swap]/[swap]]. 
  move=> E /(confluence equiv) H /E /H [x +]; exists x=> //; exact/E. 
Qed.

Lemma rwe_itr: (rw ⋅ eqv)^+ ≡ rw^+ ⋅ eqv.
Proof.
  apply/(antisym (rw ⋅ eqv)^+ )=> [|s1 s2 [x ]].
  apply/itr_ind_l1=> [|s1 s3 [s2 [x + /eqv_symm e [y /diamond_eqv/(_ e)]]]]. 
  - exact/(dot_leq (itr_ext rw) (leq_Reflexive eqv)).
  move=> s [s5 ? /eqv_symm/eqv_trans t/t ?]; exists s5=> //. 
  apply/(itr_cons rw); by exists x.
  suff: (rw^+ ≦ (fun s1 x => x ~~ s2 -> s1 ~>~+ s2)).
  - apply.
  apply/itr_ind_l1=> {s1 x} [s1 x ??|s1 x /= [y ? /[apply] ?]].
  - apply/(itr_ext (rw ⋅ eqv)); by exists x.
  apply/(itr_cons (rw ⋅ eqv)); do ? exists y=> //; exact/eqv_refl.
Qed.

Theorem econfluence s1 s2 s3: 
  s1 ~>+ s2 -> s1 ~>+ s3 -> 
  exists s4 s4', (s2 ~>+ s4 * s3 ~>+ s4' * s4 ~~ s4')%type.
Proof.
  move/(confluence diamond_rwe)=> /[swap]/[dup] ? /[-! dotx1 rw^+ s1].
  move/(dot_leq (leq_Reflexive rw^+) eqv_refl) /rwe_itr=> r /(_ _ r)[x].
  by case/rwe_itr=> y; exists y, x.
Qed.

End ERewritingSystem.
>>>>>>> 67b02cd... feat: add rewriting system theory
